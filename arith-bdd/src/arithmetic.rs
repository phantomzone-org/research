use biodivine_lib_bdd::*;
use itertools::Itertools;
use proc_macro2::TokenStream;

use crate::{codegen::codegen_multibit_output, graph::updown_bdd_from_bdd};

// Note: variables that are used together must be placed next to each other in variable array. This is because width of the resulting BDD depends on variable
// ordering. If variables that are used together are placed far apart in the ordering, the resulting BDD is very wide. In fact the width at haldway through
// the depth doubles with every bit.
//
// This is why we prefer criss cross input bit order: a0 b0 a1 b1... and not a0 a1 ... a{n-1} b0 b1 ....
//
// TODO: Variable ordering determines BDD. What's the optimal variable ordering per circuit, heuristically?
fn add(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = (0..bits)
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect();
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let mut a = vec![];
    let mut b = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b.push(vars.mk_var_by_name(&format!("b{}", i)));
    });

    // Half adder
    // c_in = 0
    let mut out = vec![];
    out.push(a[0].xor(&b[0]));
    let mut c = a[0].and(&b[0]);

    for i in 1..bits {
        // full adder
        let s = (a[i].xor(&b[i])).xor(&c);
        out.push(s);
        c = (a[i].and(&b[i])).or(&(a[i].xor(&b[i])).and(&c));
    }

    (out, vars)
}

fn sub(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = (0..bits)
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect();
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let mut a = vec![];
    let mut b = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b.push(vars.mk_var_by_name(&format!("b{}", i)));
    });

    b.iter_mut().for_each(|bb| *bb = bb.not());

    let mut out = vec![];
    let mut c = vars.mk_true();
    for i in 0..bits {
        // full adder
        let s = (a[i].xor(&b[i])).xor(&c);
        out.push(s);
        c = (a[i].and(&b[i])).or(&(a[i].xor(&b[i])).and(&c));
    }

    (out, vars)
}

fn add_sub_input_order(bits: usize) -> Vec<String> {
    (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect()
}

fn codegen_arith_op(
    word_size: usize,
    op_fn: fn(usize) -> (Vec<Bdd>, BddVariableSet),
) -> TokenStream {
    assert!(word_size.is_power_of_two());

    let (bdds, vars) = op_fn(word_size);
    let input_order = add_sub_input_order(word_size);
    let udbdds = bdds
        .iter()
        .map(|bdd| updown_bdd_from_bdd(bdd, &vars, &input_order, None))
        .collect_vec();

    codegen_multibit_output(input_order.len(), bdds.len(), &udbdds)
}

pub fn codegen_add(word_size: usize) -> TokenStream {
    codegen_arith_op(word_size, add)
}

pub fn codegen_sub(word_size: usize) -> TokenStream {
    codegen_arith_op(word_size, sub)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::updown_bdd_from_bdd;
    use crate::tests::{GGSW, bit_mask, bits_to_u32, execute, u32_to_bits};
    use itertools::Itertools;
    use rand::{RngCore, rng};

    #[test]
    fn test_add_and_sub() {
        // TODO: (jay) tests will fail for bits!=32 because add operation is defined as wrapping,
        // not mod (1<<bits)
        let bits = 32;

        let (add_bdds, add_vars) = add(bits);
        let add_input_order = add_sub_input_order(bits);
        // let udbdd =
        //     updown_bdd_from_bdd(&add_bdds[1], &add_vars, &add_input_order);
        // println!("{}", udbdd);
        let add_udbdds = add_bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &add_vars, &add_input_order, None))
            .collect_vec();

        let (sub_bdds, sub_vars) = sub(bits);
        let sub_input_order = add_input_order.clone();
        let sub_udbdds = sub_bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &sub_vars, &sub_input_order, None))
            .collect_vec();

        // println!(
        //     "Add: {}",
        //     add_bdds[bits - 1].to_dot_string(&add_vars, false)
        // );
        // println!(
        //     "Add: Stats for bit {}:\n{}",
        //     bits - 1,
        //     add_udbdds[bits - 1].stats()
        // );
        // println!(
        //     "Sub: {}",
        //     sub_bdds[bits - 1].to_dot_string(&add_vars, false)
        // );
        // println!(
        //     "Sub: Stats for bit {}:\n{}",
        //     bits - 1,
        //     sub_udbdds[bits - 1].stats()
        // );

        let bit_mask = bit_mask(bits);

        for _ in 0..1000 {
            let a = rng().next_u32() & bit_mask;
            let b = rng().next_u32() & bit_mask;

            let input_bitstring = u32_to_bits(a)
                .into_iter()
                .chain(u32_to_bits(b).into_iter())
                .collect_vec();
            let input_ggsw =
                input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

            let add_out_ggsw = add_udbdds
                .iter()
                .map(|udb| execute(udb, &input_ggsw).value() as u8)
                .collect_vec();
            let sub_out_ggsw = sub_udbdds
                .iter()
                .map(|udb| execute(udb, &input_ggsw).value() as u8)
                .collect_vec();

            let add_have_ggsw = bits_to_u32(&add_out_ggsw);
            let sub_have_ggsw = bits_to_u32(&sub_out_ggsw);
            let add_want = a.wrapping_add(b);
            let sub_want = a.wrapping_sub(b);

            assert_eq!(
                add_want, add_have_ggsw,
                "want={:b}, have{:b}",
                add_want, add_have_ggsw
            );
            assert_eq!(sub_want, sub_have_ggsw);
        }
    }
}
