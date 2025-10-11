use biodivine_lib_bdd::*;
use proc_macro2::TokenStream;

use crate::{codegen::codegen_multibit_output, graph::updown_bdd_from_bdd};

#[allow(dead_code)]
mod experimental {
    use super::*;

    /// s==true if signed otherwise s==false
    fn combined_comparitor_circuit(
        bits: usize,
    ) -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
        let vars_arr: Vec<String> = vec!["s".to_string()]
            .into_iter()
            .chain(
                (0..bits)
                    .rev()
                    .flat_map(|i| [format!("a{}", i), format!("b{}", i)]),
            )
            .collect();
        // println!("Vals={:?}", &vars_arr);
        let vars_arr_ref: Vec<&str> =
            vars_arr.iter().map(|a| a.as_str()).collect();
        let vars = BddVariableSet::new(&vars_arr_ref);
        let s = vars.mk_var_by_name("s");
        let mut a = vec![];
        let mut b = vec![];
        (0..bits).for_each(|i| {
            a.push(vars.mk_var_by_name(&format!("a{}", i)));
            b.push(vars.mk_var_by_name(&format!("b{}", i)));
        });

        let mut comp = Bdd::if_then_else(&s, &b[bits - 1].not(), &b[bits - 1])
            .and(&Bdd::if_then_else(&s, &a[bits - 1], &a[bits - 1].not()));
        let mut not_casc =
            (Bdd::if_then_else(&s, &b[bits - 1].not(), &b[bits - 1])
                .xor(&Bdd::if_then_else(&s, &a[bits - 1].not(), &a[bits - 1])))
            .not();

        for i in (0..bits - 1).rev() {
            comp = comp.or(&(b[i].and(&a[i].not())).and(&not_casc));
            not_casc = not_casc.and(&(b[i].xor(&a[i])).not());
        }

        (comp, vars)
    }
}

/// a < b
fn comparitor_circuit(a: &[Bdd], b: &[Bdd], bits: usize) -> Bdd {
    let mut comp = b[bits - 1].and(&a[bits - 1].not());
    let mut not_casc = (b[bits - 1].xor(&a[bits - 1])).not();

    for i in (0..bits - 1).rev() {
        comp = comp.or(&(b[i].and(&a[i].not())).and(&not_casc));
        not_casc = not_casc.and(&(b[i].xor(&a[i])).not());
    }

    comp
}

fn unsigned_comparitor(
    bits: usize,
) -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars_arr: Vec<String> = (0..bits)
        .rev()
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect();
    let vars_arr_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_arr_ref);
    let mut a = vec![];
    let mut b = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b.push(vars.mk_var_by_name(&format!("b{}", i)));
    });

    let comp = comparitor_circuit(&a, &b, bits);
    (comp, vars)
}

fn signed_comparitor(
    bits: usize,
) -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars_arr: Vec<String> = (0..bits)
        .rev()
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect();
    let vars_arr_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_arr_ref);
    let mut a = vec![];
    let mut b = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b.push(vars.mk_var_by_name(&format!("b{}", i)));
    });

    a[bits - 1] = a[bits - 1].not();
    b[bits - 1] = b[bits - 1].not();
    let comp = comparitor_circuit(&a, &b, bits);
    (comp, vars)
}

fn unsigned_comparitor_input_order(bits: usize) -> Vec<String> {
    (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect()
}

fn codegen_comp_op(
    word_size: usize,
    op_fn: fn(usize) -> (Bdd, BddVariableSet),
) -> TokenStream {
    assert!(word_size.is_power_of_two());

    let (bdd, vars) = op_fn(word_size);
    let input_order = unsigned_comparitor_input_order(word_size);
    let udbdds = vec![updown_bdd_from_bdd(&bdd, &vars, &input_order, None)];

    codegen_multibit_output(&udbdds)
}

pub fn codegen_unsigned_comparitor(word_size: usize) -> TokenStream {
    codegen_comp_op(word_size, unsigned_comparitor)
}

pub fn codegen_signed_comparitor(word_size: usize) -> TokenStream {
    codegen_comp_op(word_size, signed_comparitor)
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use rand::{RngCore, rng};

    use crate::{
        graph::updown_bdd_from_bdd,
        tests::{
            GGSW, bit_mask, execute, input_bits_to_bdd_var_input, uint_to_int,
        },
    };

    use super::*;

    fn unsigned_comparitor_bdd_variable_order(bits: usize) -> Vec<String> {
        (0..bits)
            .rev()
            .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
            .collect()
    }

    #[test]
    fn test_comparitors() {
        let bits = 32;
        let (unsigned_bdd, unsigned_vars) = unsigned_comparitor(bits);
        let (signed_bdd, signed_vars) = signed_comparitor(bits);

        // println!("{}", actual_bdd.to_dot_string(&var_names, false));
        let unsigned_udbdd = updown_bdd_from_bdd(
            &unsigned_bdd,
            &unsigned_vars,
            &unsigned_comparitor_input_order(bits),
            None,
        );
        let signed_udbdd = updown_bdd_from_bdd(
            &signed_bdd,
            &signed_vars,
            &unsigned_comparitor_input_order(bits),
            None,
        );

        println!("Unsigned UpDownBDD stats: {}", unsigned_udbdd.stats());
        println!("Signed UpDownBDD stats: {}", signed_udbdd.stats());

        let input_order = unsigned_comparitor_input_order(bits);
        let bdd_var_order = unsigned_comparitor_bdd_variable_order(bits);

        let bit_mask = bit_mask(bits);
        for _ in 0..1000 {
            let a = rng().next_u32() & bit_mask;
            let b = rng().next_u32() & bit_mask;

            let input_bits: Vec<u8> = [a, b]
                .iter()
                .flat_map(|v| (0..bits).map(|e| ((*v >> e) & 1) as u8))
                .collect();
            let input_bools = input_bits_to_bdd_var_input(
                &input_order,
                &bdd_var_order,
                None,
                &input_bits,
            );
            let inputs = input_bits
                .iter()
                .map(|b| GGSW::from(*b as usize))
                .collect_vec();

            let uc = a < b;
            let ic = uint_to_int(a, bits) < uint_to_int(b, bits);

            let unsigned_bdd_out =
                unsigned_bdd.eval_in(&BddValuation::new(input_bools.clone()));
            let signed_bdd_out =
                signed_bdd.eval_in(&BddValuation::new(input_bools));
            let unsigned_out = execute(&unsigned_udbdd, &inputs);
            let signed_out = execute(&signed_udbdd, &inputs);

            assert_eq!(unsigned_out.value() == 1, unsigned_bdd_out);
            assert_eq!(signed_out.value() == 1, signed_bdd_out);
            assert_eq!(
                uc,
                unsigned_out.value() == 1,
                "expected {uc} but got {} for a={a} > b={b}",
                unsigned_out.value() == 1
            );
            // if a == (1 << (bits - 1)) && b == (1 << (bits - 1)) {
            assert_eq!(
                ic,
                signed_out.value() == 1,
                "expected {ic} but got {} for a={a} > b={b}",
                signed_out.value() == 1
            )
        }
    }
}
