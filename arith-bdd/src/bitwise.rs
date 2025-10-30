use biodivine_lib_bdd::*;
use itertools::Itertools;
use proc_macro2::TokenStream;

use crate::codegen::codegen_multibit_output;
use crate::graph::updown_bdd_from_bdd;

#[allow(non_camel_case_types)]
enum BIT_OP {
    AND,
    OR,
    XOR,
}

fn bitwise_circuit(
    bits: usize,
    bit_op: BIT_OP,
) -> (
    Vec<biodivine_lib_bdd::Bdd>,
    biodivine_lib_bdd::BddVariableSet,
) {
    // variables are in the following order: a0,b0,a1,b1,....
    let variables = BddVariableSet::new_anonymous((bits * 2) as u16);
    let vars = variables.variables();
    let mut out = vec![];
    for i in 0..bits {
        let a = variables.mk_var(vars[2 * i]);
        let b = variables.mk_var(vars[2 * i + 1]);
        let o = match bit_op {
            BIT_OP::AND => a.and(&b),
            BIT_OP::XOR => a.xor(&b),
            BIT_OP::OR => a.or(&b),
        };
        out.push(o);
    }

    (out, variables)
}

fn input_order(bits: usize) -> Vec<String> {
    let mut out = vec![];
    // desired input order: a0,a1,...,an-1, b0, b1,..., bn-1
    // recall that all variables x_{i} where i is even are assigned to bits of a and all vairables x_{j} where j is odd are assigned to bits of b ( i.e. variable ordering of the bdd circuit is assumed to be interleaved)
    for i in (0..bits * 2).filter(|v| v & 1 != 1) {
        out.push(format!("x_{}", i));
    }
    for i in (0..bits * 2).filter(|v| v & 1 == 1) {
        out.push(format!("x_{}", i));
    }
    out
}

fn codegen_bitwise_op(word_size: usize, bit_op: BIT_OP) -> TokenStream {
    assert!(word_size.is_power_of_two());

    let (bdds, vars) = bitwise_circuit(word_size, bit_op);
    let input_order = input_order(word_size);
    let udbdds = bdds
        .iter()
        .map(|bdd| updown_bdd_from_bdd(bdd, &vars, &input_order, None))
        .collect_vec();

    codegen_multibit_output(&udbdds)
}

pub fn codegen_and(word_size: usize) -> TokenStream {
    codegen_bitwise_op(word_size, BIT_OP::AND)
}

pub fn codegen_or(word_size: usize) -> TokenStream {
    codegen_bitwise_op(word_size, BIT_OP::OR)
}

pub fn codegen_xor(word_size: usize) -> TokenStream {
    codegen_bitwise_op(word_size, BIT_OP::XOR)
}

#[cfg(test)]
mod tests {
    use std::ops::{BitAnd, BitOr, BitXor};

    use itertools::Itertools;

    use crate::{
        graph::updown_bdd_from_bdd,
        tests::{GGSW, bits_to_u32, execute},
    };
    use rand::{Rng, distr::Uniform, rng};

    use super::*;

    #[test]
    fn test_bitwise_ops() {
        let bits = 32;
        let (and_bdd, and_vars) = bitwise_circuit(bits, BIT_OP::AND);
        let (or_bdd, or_vars) = bitwise_circuit(bits, BIT_OP::OR);
        let (xor_bdd, xor_vars) = bitwise_circuit(bits, BIT_OP::XOR);
        let bitwise_input_order = input_order(bits);

        let and_udbdds = and_bdd
            .iter()
            .map(|bdd| {
                updown_bdd_from_bdd(bdd, &and_vars, &bitwise_input_order, None)
            })
            .collect_vec();
        let or_udbdds = or_bdd
            .iter()
            .map(|bdd| {
                updown_bdd_from_bdd(bdd, &or_vars, &bitwise_input_order, None)
            })
            .collect_vec();
        let xor_udbdds = xor_bdd
            .iter()
            .map(|bdd| {
                updown_bdd_from_bdd(bdd, &xor_vars, &bitwise_input_order, None)
            })
            .collect_vec();

        // println!("And UpDownBDD stats:\n{}", and_udbdds[bits - 1].stats());
        // println!("Or UpDownBDD stats: \n{}", or_udbdds[bits - 1].stats());
        // println!("Xor UpDownBDD stats:\n{}", xor_udbdds[bits - 1].stats());

        let iterations = 100;
        let mut max = u32::MAX;
        if bits < 32 {
            max = 1u32 << bits;
        }

        let dist = Uniform::new_inclusive(0, max).unwrap();
        for a in rng().sample_iter(&dist).take(iterations) {
            for b in rng().sample_iter(&dist).take(iterations) {
                let input_bits: Vec<u8> = [a, b]
                    .iter()
                    .flat_map(|v| (0..bits).map(|e| ((*v >> e) & 1) as u8))
                    .collect();
                let inputs = input_bits
                    .iter()
                    .map(|&bit| GGSW::from((bit == 1) as u8))
                    .collect_vec();

                let or_c = a.bitor(b);
                let and_c = a.bitand(b);
                let xor_c = a.bitxor(b);

                let and_outs = and_udbdds
                    .iter()
                    .map(|bdd| execute(bdd, &inputs).value() as u8)
                    .collect_vec();
                let or_outs = or_udbdds
                    .iter()
                    .map(|bdd| execute(bdd, &inputs).value() as u8)
                    .collect_vec();
                let xor_outs = xor_udbdds
                    .iter()
                    .map(|bdd| execute(bdd, &inputs).value() as u8)
                    .collect_vec();

                let and_have = bits_to_u32(&and_outs);
                let or_have = bits_to_u32(&or_outs);
                let xor_have = bits_to_u32(&xor_outs);

                assert_eq!(and_have, and_c);
                assert_eq!(or_have, or_c);
                assert_eq!(xor_have, xor_c);
            }
        }
    }
}
