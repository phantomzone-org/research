use std::fmt::Display;

use biodivine_lib_bdd::*;
use itertools::Itertools;
use proc_macro2::TokenStream;

use crate::{codegen::codegen_multibit_output, graph::updown_bdd_from_bdd};

#[derive(Clone, Copy, Debug)]
pub(crate) enum ShiftOp {
    SLL,
    SRL,
    SRA,
}

impl Display for ShiftOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ShiftOp::SRA => write!(f, "sra"),
            ShiftOp::SRL => write!(f, "srl"),
            ShiftOp::SLL => write!(f, "sll"),
        }
    }
}

/// Input order: a0,a1,..an,s0,s1...,sk
fn input_order(input_bits: usize, shift_bits: usize) -> Vec<String> {
    (0..input_bits)
        .map(|i| format!("x_{}", i + shift_bits))
        .chain((0..shift_bits).map(|i| format!("x_{}", i)))
        .collect()
}

fn shift_circuit(
    input_bits: usize,
    shift_bits: usize,
    shift_op: ShiftOp,
) -> (
    Vec<biodivine_lib_bdd::Bdd>,
    biodivine_lib_bdd::BddVariableSet,
) {
    let variables =
        BddVariableSet::new_anonymous((input_bits + shift_bits) as u16);
    let vars = variables.variables();

    let mut a = vec![];
    let mut b = vec![];
    (0..shift_bits).for_each(|i| {
        b.push(variables.mk_var(vars[i]));
    });
    (0..input_bits).for_each(|i| {
        a.push(variables.mk_var(vars[shift_bits + i]));
    });

    let mk_false = variables.mk_false();
    for i in 0..shift_bits {
        let jump = 1 << i;

        let a_clone = a.clone();
        for j in 0..input_bits {
            let (if_true_var, if_false_var) = match shift_op {
                ShiftOp::SLL => {
                    let if_true_var = {
                        if jump > j {
                            &mk_false
                        } else {
                            &a_clone[j - jump]
                        }
                    };
                    let if_false_var = &a_clone[j];
                    (if_true_var, if_false_var)
                }
                ShiftOp::SRL => {
                    let if_true_var = {
                        if jump + j >= input_bits {
                            &mk_false
                        } else {
                            &a_clone[j + jump]
                        }
                    };
                    let if_false_var = &a_clone[j];
                    (if_true_var, if_false_var)
                }
                ShiftOp::SRA => {
                    let if_true_var = {
                        if jump + j >= input_bits {
                            &a_clone[input_bits - 1]
                        } else {
                            &a_clone[j + jump]
                        }
                    };
                    let if_false_var = &a_clone[j];
                    (if_true_var, if_false_var)
                }
            };

            a[j] = Bdd::if_then_else(&b[i], &if_true_var, &if_false_var);
        }
    }
    (a, variables)
}

fn codegen_shift(word_size: usize, shift_op: ShiftOp) -> TokenStream {
    assert!(word_size.is_power_of_two());
    let shift_bits = (usize::BITS - word_size.leading_zeros() - 1) as usize;

    let (bdds, vars) = shift_circuit(word_size, shift_bits, shift_op);
    let input_order = input_order(word_size, shift_bits);
    let udbdds = bdds
        .iter()
        .map(|bdd| updown_bdd_from_bdd(bdd, &vars, &input_order, None))
        .collect_vec();

    codegen_multibit_output(input_order.len(), bdds.len(), &udbdds)
}

pub fn codegen_sll(word_size: usize) -> TokenStream {
    codegen_shift(word_size, ShiftOp::SLL)
}

pub fn codegen_srl(word_size: usize) -> TokenStream {
    codegen_shift(word_size, ShiftOp::SRL)
}

pub fn codegen_sra(word_size: usize) -> TokenStream {
    codegen_shift(word_size, ShiftOp::SRA)
}

#[allow(dead_code)]
mod experimental {
    use super::*;

    fn shift_circuit_combined_input_order(
        input_bits: usize,
        shift_bits: usize,
    ) -> Vec<String> {
        vec![format!("x_{}", shift_bits), format!("x_{}", shift_bits + 1)]
            .into_iter()
            .chain((0..shift_bits).map(|i| format!("x_{}", i)))
            .chain((0..input_bits).map(|i| format!("x_{}", i + shift_bits)))
            .collect()
    }

    fn shift_circuit_combined(
        input_bits: usize,
        shift_bits: usize,
    ) -> (
        Vec<biodivine_lib_bdd::Bdd>,
        biodivine_lib_bdd::BddVariableSet,
    ) {
        let variables =
            BddVariableSet::new_anonymous((2 + input_bits + shift_bits) as u16);
        let vars = variables.variables();

        let mut a = vec![];
        let mut b = vec![];
        let s0 = variables.mk_var(vars[shift_bits]);
        let s1 = variables.mk_var(vars[shift_bits + 1]);
        (0..shift_bits).for_each(|i| {
            b.push(variables.mk_var(vars[i]));
        });
        (0..input_bits).for_each(|i| {
            a.push(variables.mk_var(vars[shift_bits + i + 2]));
        });

        let mk_false = variables.mk_false();
        for i in 0..shift_bits {
            let jump = 1 << i;

            let a_clone = a.clone();
            for j in 0..input_bits {
                // 00 | 10 => SLL
                // 01      => SRL
                // 11      => SRA

                let sll_if_true = if jump > j {
                    &mk_false
                } else {
                    &a_clone[j - jump]
                };

                let sr_if_true = if jump + j >= input_bits {
                    &Bdd::if_then_else(&s0, &a_clone[input_bits - 1], &mk_false)
                } else {
                    &a_clone[j + jump]
                };

                let if_true_var =
                    Bdd::if_then_else(&s1, sr_if_true, sll_if_true);

                a[j] = Bdd::if_then_else(&b[i], &if_true_var, &a_clone[j]);
            }
        }
        (a, variables)
    }
}

#[cfg(test)]
mod tests {
    use rand::{Rng, rng};

    use super::*;
    use crate::tests::*;

    #[test]
    fn test_shift_ops() {
        let bits = 32;
        let shift_bits = 5;

        for op_type in [ShiftOp::SLL, ShiftOp::SRL, ShiftOp::SRA] {
            let (bdds, vars) = shift_circuit(bits, shift_bits, op_type);

            let _index_most_expensive = match op_type {
                ShiftOp::SLL => bits - 1,
                ShiftOp::SRA | ShiftOp::SRL => 0,
            };

            // println!(
            //     "{}",
            //     bdds[index_most_expensive].to_dot_string(&vars, false)
            // );
            // bdds.iter().for_each(|bdd| {
            //     println!("{}", bdd.to_dot_string(&vars, false));
            // });

            let udbdds = bdds
                .iter()
                .map(|bdd| {
                    updown_bdd_from_bdd(
                        bdd,
                        &vars,
                        &input_order(bits, shift_bits),
                        None,
                    )
                })
                .collect_vec();

            // println!("{}", udbdds[index_most_expensive].stats());
            // udbdds.iter().for_each(|udbb| {
            //     println!("{}", udbb.stats());
            // });

            for value in rng().random_iter::<u32>().take(1000) {
                for shift in 0..1 << shift_bits {
                    let inputs_bool: Vec<bool> = (0..shift_bits)
                        .map(|i| (shift >> i) & 1 == 1)
                        .chain((0..bits).map(|i| (value >> i) & 1 == 1))
                        .collect();
                    let out_bdd: Vec<bool> = bdds
                        .iter()
                        .map(|bdd| {
                            bdd.eval_in(&BddValuation::new(inputs_bool.clone()))
                        })
                        .collect();

                    let inputs_bool_ubdds: Vec<GGSW> = (0..bits)
                        .map(|i| (value >> i) & 1)
                        .chain((0..shift_bits).map(|i| (shift >> i) & 1))
                        .map(|b| GGSW::from(b as u8))
                        .collect();
                    let out_ubdds = udbdds
                        .iter()
                        .map(|ubdd| {
                            execute(ubdd, &inputs_bool_ubdds).value() == 1
                        })
                        .collect_vec();

                    // println!("Out {:?}", &out_bdd);
                    let have_out_bdds = out_bdd
                        .iter()
                        .enumerate()
                        .fold(0u32, |res, (index, b)| {
                            res + ((*b as u32) << index)
                        });
                    let have_out_ubdds = out_ubdds
                        .iter()
                        .enumerate()
                        .fold(0u32, |res, (index, b)| {
                            res + ((*b as u32) << index)
                        });

                    let want_out = match op_type {
                        ShiftOp::SLL => value << shift,
                        ShiftOp::SRL => value >> shift,
                        ShiftOp::SRA => ((value as i32) >> (shift)) as u32,
                    };

                    assert_eq!(have_out_bdds, have_out_ubdds);

                    assert_eq!(
                        have_out_ubdds, want_out,
                        "Failed at {:#b} {:?} {shift}. have_out={:#b}, want_out={:#b}",
                        value, op_type, have_out_bdds, want_out
                    );
                }
            }
        }
    }
}
