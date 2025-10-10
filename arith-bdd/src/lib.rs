use std::collections::{HashMap, HashSet};
use std::{fmt::Display, iter};
// use petgraph::dot::dot_parser::
use biodivine_lib_bdd::*;
use itertools::Itertools;
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::Graph;
use petgraph::algo::toposort;
use petgraph::dot::Dot;
use petgraph::visit::NodeRef;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};
use proc_macro2::TokenStream;
use quote::quote;
use syn::parse_str;

// Note on variable ordering:
//
// The size of BDD is very dependent on variable ordering. For example, the BDD of adder circuit is exponential in width with following variable order: a0,a1, ...,a31, b0, b1, ..., b31. And constant in width and linear in depth with variable ordering: a0, b0, a1, b1, ..., a31, b31.
//
// This can be explained by modelling BDD as a serial-read bit processor. In the addition function, two bits ai,bi are needed at once to compute the summation si and carry forward c{i+1}. If the bit processor is supplied first with a and then with b then the processor (the BDD) needs to store a in its memory. BDD stores a in its memory by constructing a sub-bdd for recreating value of a (i.e. a sub-tree with depth n=log_2(a) with 2^n terminal nodes) and subsequently uses values of bi, as they are read, to reduce to the output value.
//
// On the other hand, if the processor reads bits of a and b in interleaved manner (i.e. a0,b0,a1,b1...) then the BDD is not forced to reconstruct a. It can forget ai, bi right after they are read. This results in a BDD with a linear structure.
//
// Comment on variable orderings below:
//         - Addition, subtraction have interleaved variable ordering since in the function flow ai,bi are needed once, together.
//         - left/right logical and right arithmetic circuits have variable ordering as: s0,..sk, a0,...,an where `si`s are bits of shift value and `ai`s are bits of input value. This is because function flow of the shift operation should first construct the shift and then set the bit at output index as the bit at shift index. Thus, for resulting BDD to near optimal it shift bits must be fed first and then the bits of the input value.
//
// TODO:
//      - Although I have eye rolled to check that BDD circuits produced below are optimal, but I'm
//      yet ascertain this claim.
//      - Question: there's literature to optimise ROBDDs using techniques like subgraph isomorphism
//      elimination or variable elimination. Do running any of these optimisation techniques not
//      reduce the size of our circuits? IDK!
//
// References:
// - https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf (section 3.2)

//
// Note on combined circuits:
//
// I've added combined circuits for multiple routines. For instance, a combined circuit for add+sub (called add_sub) that takes a signal bit, in addition to 2xu32 values, and outputs either, based on signal bit, result of addition or subtraction. In case of add_sub, it does not lead to substantial saving because addition circuit is quite different from subtraction circuit (rhs is negated in 2's complement subtraction).
//
// But in other cases it does lead to savings. For example, combined comparitor (called `combined_comparitor_circuit`) is same as unsigned/signed comparitor with 1 additional depth. This is because the only difference between, signed and unsigned comparison is that MSB in signed comparison are flipped. In addition to 2xu32 inputs, the circuit requires a single bit to indicate whether the operation is signed comparison or unsigned comparison.
//
// Combined shift circuit (called `shift_circuit_combined`) also benefits from the combination.
//
// However, combined circuits require additional signal bits. These signal bits will have to retrieved from the encrypted ROM. It's likely that the gains from combined circuit will not offset the cost to retrieve signal bits from the RAM and circuit bootstrap them.

// TODO:
//     - implement the test for `combined_comparitor_circuit`
//     - implement a routine in `main.rs` to output required generated circuit files for phantom
//     - implement PC update routine and tests in phantom
//     -
//
//

// Note on PC update:
//
// PC update is implemented as a single circuit, which eliminates the need of homomorphic selection
// later.
//
// JAL has 20 bit immediate where as all other operations (including JALR) have 12 bit immediates. This is
// problematic because the RAM will have to pay the cost of retrieving a 20 bit immediate value,
// irrespective of what operation it is. One potential solution is to limit JAL to 12 bit value,
// which will restrict its jumps to +/- 2Kib. We'll have to investigate this furter.
//
// For now, PC update circuit assumes 20 bit immediates for all operations.
//
//
// Notes in risc-v:
// 1. Register-Immediate Integer instructions have 12 bit imm.
// 2. Operation LUI, takes 20 immediate and sets it as the 20 MSB of rd
// 3. Operation AUIPC, takes 20 bit immediate shift it to form a 32 bit value, filling the lowest
//    12 bits with 0s. Then adds the 32 bit value to PC and sets the output as rd
// 4. JAL, JALR instructions mutate both the PC and rd.
//      - JAL has 20 bit immediate whereas other PC update ops, including JALR, have 12 bit
//      immediates. All immediates are sign extended.
//      - Both JAL, JALR set rd to pc+4 and set PC to jump target
//      - jump target = sign_extend(imm)+pc. For JALR, LSB of jump target is set of 0
// 5. Condition branch instructions BNE, BEQ, BLT[U], BGE[U] don't update rd

/// Input order: a0,a1,..an,s0,s1...,sk
fn shift_circuit_input_order(
    input_bits: usize,
    shift_bits: usize,
) -> Vec<String> {
    (0..input_bits)
        .map(|i| format!("x_{}", i + shift_bits))
        .chain((0..shift_bits).map(|i| format!("x_{}", i)))
        .collect()
}

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

#[derive(Clone, Copy, Debug)]
enum ShiftOp {
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

            let if_true_var = Bdd::if_then_else(&s1, sr_if_true, sll_if_true);

            a[j] = Bdd::if_then_else(&b[i], &if_true_var, &a_clone[j]);
        }
    }
    (a, variables)
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

fn bitwise_circuit_input_order(bits: usize) -> Vec<String> {
    let mut out = vec![];
    // desired input order: a0,a1,...,an-1, b0, b1,..., bn-1
    for i in (0..bits * 2).filter(|v| v & 1 != 1) {
        out.push(format!("x_{}", i));
    }
    for i in (0..bits * 2).filter(|v| v & 1 == 1) {
        out.push(format!("x_{}", i));
    }
    out
}

/// s0 | IL(rs1,rs2) | s1 | s2 | s3 | s4 | imm[0] | pc[0] | s5 | IL(imm[1:20], pc[1:20]) |
/// pc[21:32]
///
/// s0 == 1 if op==(<s or >=s) else 0
/// s1 == 1 if op==(is_eq OR is_neq) else 0
/// s2 == 1 if op==(is not variant of ==, <s, <u) else 0
/// s3 == 1 if op==JALR|JAL else 0
/// s4 == 1 if op==(is any of branching ops) else 0
/// s5 == 1 if op==JALR else 0
fn pc_update(// bits: usize,
) -> (
    Vec<biodivine_lib_bdd::Bdd>,
    biodivine_lib_bdd::BddVariableSet,
) {
    let bits = 32;
    let vars_arr: Vec<String> = vec!["s2".to_string()]
        .into_iter()
        .chain(
            (0..bits)
                .rev()
                .flat_map(|i| [format!("rs1_{}", i), format!("rs2_{}", i)])
                .chain(
                    vec![
                        "s3".to_string(),
                        "s2_c".to_string(),
                        "s1".to_string(),
                        "s0".to_string(),
                        "s2_2c".to_string(),
                        "s1_c".to_string(),
                        "s0_c".to_string(),
                    ]
                    .into_iter()
                    .chain(
                        (0..20)
                            .flat_map(|i| {
                                [format!("imm{}", i), format!("pc{}", i)]
                            })
                            .chain((20..32).map(|i| format!("pc{}", i))),
                    ),
                ),
        )
        .collect();
    // println!("Vals={:?}", &vars_arr);
    let vars_arr_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_arr_ref);
    let s0 = vars.mk_var_by_name("s0"); // <u | <s
    let s1 = vars.mk_var_by_name("s1"); // == | (<u | <s)
    let s2 = vars.mk_var_by_name("s2"); // ==true if ne ops, otherwse false
    let s3 = vars.mk_var_by_name("s3"); // ==true if JALR | JAL, otherwise false
    // aliases, `c` stands for copy
    let s0_c = vars.mk_var_by_name("s0_c");
    let s1_c = vars.mk_var_by_name("s1_c");
    let s2_c = vars.mk_var_by_name("s2_c");
    let s2_2c = vars.mk_var_by_name("s2_2c");

    let mut rs1 = vec![];
    let mut rs2 = vec![];
    (0..bits).for_each(|i| {
        rs1.push(vars.mk_var_by_name(&format!("rs1_{}", i)));
        rs2.push(vars.mk_var_by_name(&format!("rs2_{}", i)));
    });

    let mut pc = vec![];
    let mut imm = vec![];
    (0..32).for_each(|i| {
        pc.push(vars.mk_var_by_name(&format!("pc{}", i)));
        if i < 20 {
            imm.push(vars.mk_var_by_name(&format!("imm{}", i)));
        }
    });

    // ==== Circuit begins ====

    let mut comp =
        Bdd::if_then_else(&s2, &rs2[bits - 1].not(), &rs2[bits - 1]).and(
            &Bdd::if_then_else(&s2, &rs1[bits - 1], &rs1[bits - 1].not()),
        );
    let mut not_casc =
        (Bdd::if_then_else(&s2, &rs2[bits - 1].not(), &rs2[bits - 1]).xor(
            &Bdd::if_then_else(&s2, &rs1[bits - 1].not(), &rs1[bits - 1]),
        ))
        .not();

    for i in (0..bits - 1).rev() {
        comp = comp.or(&(rs2[i].and(&rs1[i].not())).and(&not_casc));
        not_casc = not_casc.and(&(rs2[i].xor(&rs1[i])).not());
    }

    // if not_casc == 1, then rs1==rs2, else rs1!=rs2
    // if comp == 1, then rs1<rs2, else rs1>=rs2

    let choose_lt_ge = Bdd::if_then_else(&s3, &comp.not(), &comp);
    let choose_ne_eq = Bdd::if_then_else(&s2_c, &not_casc.not(), &not_casc);
    let left_root = Bdd::if_then_else(&s1, &choose_lt_ge, &choose_ne_eq);
    // right_root = s1
    let is_op = Bdd::if_then_else(&s0, &s1, &left_root);

    // 0th bit
    let mut out = vec![];
    let rhs = Bdd::if_then_else(&is_op, &imm[0], &vars.mk_false());
    let mut c = pc[0].and(&rhs);
    let is_jalr = s0_c.and(&s1_c.and(&s2_2c));
    out.push(Bdd::if_then_else(
        &is_jalr,
        &vars.mk_false(),
        &pc[0].xor(&rhs),
    ));

    // 1st bit
    let rhs = Bdd::if_then_else(&is_op, &imm[1], &vars.mk_false());
    out.push((pc[1].xor(&rhs)).xor(&c));
    c = (pc[1].and(&rhs)).or(&(pc[1].xor(&rhs)).and(&c));

    // 2nd bit
    let rhs = Bdd::if_then_else(&is_op, &imm[2], &vars.mk_true());
    out.push((pc[2].xor(&rhs)).xor(&c));
    c = (pc[2].and(&rhs)).or(&(pc[2].xor(&rhs)).and(&c));

    // [3:19] bit
    for i in 3..20 {
        let rhs = Bdd::if_then_else(&is_op, &imm[i], &vars.mk_false());
        out.push((pc[i].xor(&rhs)).xor(&c));
        c = (pc[i].and(&rhs)).or(&(pc[i].xor(&rhs)).and(&c));
    }
    let imm_sign = Bdd::if_then_else(&is_op, &imm[19], &vars.mk_false());
    for i in 20..32 {
        out.push((pc[i].xor(&imm_sign)).xor(&c));
        c = (pc[i].and(&imm_sign)).or(&(pc[i].xor(&imm_sign)).and(&c));
    }

    (out, vars)
}

fn pc_update_input_order() -> (Vec<String>, HashMap<String, String>) {
    let bits = 32;
    let mut out = vec![
        "s0".to_string(),
        "s1".to_string(),
        "s2".to_string(),
        "s3".to_string(),
    ];
    (0..bits).for_each(|i| {
        out.push(format!("rs1_{}", i));
    });
    (0..bits).for_each(|i| {
        out.push(format!("rs2_{}", i));
    });
    (0..bits).for_each(|i| {
        out.push(format!("pc{}", i));
    });
    (0..20).for_each(|i| {
        out.push(format!("imm{}", i));
    });

    let mut alias_map = HashMap::new();
    alias_map.insert("s2_c".to_string(), "s2".to_string());
    alias_map.insert("s2_2c".to_string(), "s2".to_string());
    alias_map.insert("s0_c".to_string(), "s0".to_string());
    alias_map.insert("s1_c".to_string(), "s1".to_string());

    (out, alias_map)
}

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
    let vars_arr_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
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

fn unsigned_comparitor_bdd_variable_order(bits: usize) -> Vec<String> {
    (0..bits)
        .rev()
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect()
}

fn add_sub(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = vec![format!("s")]
        .into_iter()
        .chain((0..bits).flat_map(|i| [format!("a{}", i), format!("b{}", i)]))
        .collect();
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let s = vars.mk_var_by_name(&format!("s"));
    let mut a = vec![];
    let mut b = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b.push(vars.mk_var_by_name(&format!("b{}", i)));
    });

    let mut out = vec![];
    let mut c = s.clone();
    for i in 0..bits {
        // full adder
        let bi = Bdd::if_then_else(&s, &b[i].not(), &b[i]);
        let s = (a[i].xor(&bi)).xor(&c);
        out.push(s);
        c = (a[i].and(&bi)).or(&(a[i].xor(&bi)).and(&c));
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

fn adder_input_order(bits: usize) -> Vec<String> {
    (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect()
}

fn add_sub_input_order(bits: usize) -> Vec<String> {
    vec![format!("s")]
        .into_iter()
        .chain(
            (0..bits)
                .map(|i| format!("a{}", i))
                .chain((0..bits).map(|i| format!("b{}", i))),
        )
        .collect()
}

fn levels_for_graph(graph: &Graph<String, i32>) -> HashMap<NodeIndex, usize> {
    let top_sort = toposort(graph, Default::default()).unwrap();

    let mut level_map = HashMap::new();

    for i in 0..top_sort.len() {
        let mut level = 0;
        for incoming_edge in
            graph.edges_directed(top_sort[i], petgraph::Direction::Incoming)
        {
            let pred = incoming_edge.source();
            level = std::cmp::max(level, *level_map.get(&pred).unwrap() + 1);
        }
        assert!(level_map.insert(top_sort[i], level).is_none())
    }

    level_map
}

fn levelise_graph(
    graph: &mut Graph<String, i32>,
    levels: HashMap<NodeIndex, usize>,
) {
    let max_level = *levels.values().max().unwrap();
    for lvl in 0..max_level + 1 {
        for (node, _) in levels.iter().filter(|(_, l)| **l == lvl) {
            let node_weight = graph.node_weight(*node).unwrap().clone();

            let mut max_lvl_to_reach = lvl;
            let mut add_edges = vec![];
            let mut delete_edges = vec![];
            for out in graph.edges_directed(*node, Outgoing) {
                let node2 = out.target();
                let lvl_child = *levels.get(&node2).unwrap();
                max_lvl_to_reach = std::cmp::max(max_lvl_to_reach, lvl_child);
                add_edges.push((node2, lvl_child, *out.weight()));
                delete_edges.push(out.id());
            }

            // println!("{}: {}, {}", node_weight, lvl, max_lvl_to_reach);

            // delete old edges
            for e in delete_edges {
                graph.remove_edge(e);
            }

            // add dummy nodes
            // start node is at level = lvl
            let mut start = *node;
            for l in lvl + 1..max_lvl_to_reach + 1 {
                add_edges.iter().filter(|(_, cl, _)| *cl == l).for_each(
                    |(n, _, we)| {
                        graph.add_edge(start, *n, *we);
                    },
                );

                if l < max_lvl_to_reach {
                    let next = graph.add_node(node_weight.clone());
                    graph.add_edge(start, next, 2); // edge weight 2 implies copy
                    start = next;
                }
            }
        }
    }
}

fn translate_node_tag_to_input_index(
    node_tag: &String,
    input_order: &[String],
    alias_map: Option<&HashMap<String, String>>,
) -> usize {
    let dealiased_tag = alias_map
        .as_ref()
        .and_then(|m| m.get(node_tag).cloned())
        .unwrap_or(node_tag.clone());
    let input_index = input_order
        .iter()
        .position(|t| &dealiased_tag == t)
        .unwrap();

    input_index
}

// input_order: order of the variables as expected in the input array at evaluation
fn updown_bdd_from_bdd(
    bdd: &Bdd,
    vars: &BddVariableSet,
    input_order: &[String],
    alias_map: Option<&HashMap<String, String>>,
) -> UpDownBDD2 {
    let var_names = vars.variable_names();
    if var_names.len() != (bdd.num_vars() as usize) {
        panic!(
            "Bdd is incompatible with the variable set ({} vs. {} variables)",
            bdd.num_vars(),
            var_names.len()
        );
    }

    // Invert the BDD
    let mut graph = DiGraph::new();
    // Bdd pointer index -> NodeIndex
    let mut bdd_index_to_node_index = HashMap::new();
    let terminal_node0 = graph.add_node("0".to_string());
    let terminal_node1 = graph.add_node("1".to_string());
    bdd_index_to_node_index.insert(0, terminal_node0);
    bdd_index_to_node_index.insert(1, terminal_node1);
    // bdd.pointers().take(2).for_each(f);
    for node_pointer in bdd.pointers().skip(2) {
        // bdd's index must not repeat
        assert!(
            bdd_index_to_node_index
                .insert(
                    node_pointer.to_index(),
                    graph.add_node(
                        var_names[bdd.var_of(node_pointer).to_index()]
                            .to_string()
                    ),
                )
                .is_none()
        );
    }
    for node_pointer in bdd.pointers().skip(2) {
        let curr_node = bdd_index_to_node_index
            .get(&node_pointer.to_index())
            .unwrap();

        let high_link = bdd.high_link_of(node_pointer);
        let high_node =
            bdd_index_to_node_index.get(&high_link.to_index()).unwrap();
        // directed edge from high link node to curr node
        graph.add_edge(*high_node, *curr_node, 1);

        let low_link = bdd.low_link_of(node_pointer);
        let low_node =
            bdd_index_to_node_index.get(&low_link.to_index()).unwrap();
        // directed edge from low link node to curr node
        graph.add_edge(*low_node, *curr_node, 0);
    }

    // levelise the inverset BDD graph s.t. edge only exists between nodes that in consecutive
    // levels. We call the resulting graph: levelised graph
    {
        let levels = levels_for_graph(&graph);
        levelise_graph(&mut graph, levels);
        // println!("levelised udbdd {}", Dot::with_config(&graph, &[]));
    }

    // ==== process the levelised graph as a state vector machine ====

    let levels = levels_for_graph(&graph);
    let max_level = *levels.values().max().unwrap();
    let mut levels_to_nodes_map = HashMap::new();
    let mut max_width = 2;
    for l in 0..max_level + 1 {
        let set: HashSet<NodeIndex> = levels
            .iter()
            .filter(|(_, nl)| **nl == l)
            .map(|(n, _)| *n)
            .collect();
        max_width = std::cmp::max(max_width, set.len());
        levels_to_nodes_map.insert(l, set);
    }

    // {
    //     println!("Levels maps: ");
    //     for l in 0..max_level + 1 {
    //         println!("  {l}: {:?}", levels_to_nodes_map.get(&l).unwrap());
    //     }
    // }

    assert_eq!(
        levels_to_nodes_map.get(&0).unwrap(),
        &HashSet::from_iter([NodeIndex::new(0), NodeIndex::new(1)].into_iter())
    );
    let mut nodes_to_outpos = HashMap::new();
    nodes_to_outpos.insert(NodeIndex::new(0), 0usize);
    nodes_to_outpos.insert(NodeIndex::new(1), 1usize);

    let mut level_nodes = vec![];
    // skip the first and the last level
    for l in 1..max_level {
        let nodes_at_lvl = levels_to_nodes_map.get(&l).unwrap();
        let mut pos_set: HashSet<usize> = HashSet::from_iter(0usize..max_width);

        // Nodes are placed sorted by output position
        let mut curr_level = vec![Node::None; max_width];

        // handle copy nodes
        nodes_at_lvl.iter().filter_map(|n| {
            let incoming_edges =
                graph.edges_directed(*n, Incoming).collect_vec();
            assert!(incoming_edges.len() <= 2);
            if incoming_edges.len() == 1 {
                assert!(
                    incoming_edges[0].weight() == &2,
                    "Node has one incoming edge but with weight not equal to 2"
                );
                return Some((incoming_edges[0].source(), *n));
            }
            None
        }).for_each(|(parent_node, copy_node)| {
                let parent_pos = *nodes_to_outpos.get(&parent_node).unwrap();
                // println!("Copy node:{:?}, Parent node:{:?}, Parent Pos:{}, Parent lvl:{}", copy_node, parent_node, parent_pos, levels.get(&parent_node).unwrap());
                assert!(pos_set.remove(&parent_pos)==true, "Copy node pos is inuse but some other copy node");

                let node_weight = graph.node_weight(copy_node).unwrap().clone();
                curr_level[parent_pos]=Node::Copy(CopyNode::new(node_weight, parent_node, copy_node, parent_pos ));

                nodes_to_outpos.insert(copy_node, parent_pos);
            });

        // handle rest of the nodes
        nodes_at_lvl
            .iter()
            .filter_map(|n| {
                let mut incoming_edges =
                    graph.edges_directed(*n, Incoming).collect_vec();
                if incoming_edges.len() == 2 {
                    // sort edges: low_index, high_index
                    incoming_edges.sort_by(|a, b| a.weight().cmp(b.weight()));
                    assert!(
                        incoming_edges[0].weight() == &0
                            && incoming_edges[1].weight() == &1
                    );
                    // (low_node, high_node, curr_node)
                    return Some((
                        incoming_edges[0].source(),
                        incoming_edges[1].source(),
                        *n,
                    ));
                }
                None
            })
            .for_each(|(low_node, high_node, curr_node)| {
                let curr_pos = pos_set.iter().next().cloned().expect("Positions ran out before each node at level has a position");
                assert!(pos_set.remove(&curr_pos));

                let high_index =*nodes_to_outpos.get(&high_node).unwrap();
                let low_index =* nodes_to_outpos.get(&low_node).unwrap();
                let node_weight = graph.node_weight(curr_node).unwrap().clone();
                let input_index = translate_node_tag_to_input_index(&node_weight, input_order, alias_map);
                curr_level[curr_pos] = Node::OpNode(OpNode::new(node_weight, curr_node,high_node ,low_node, curr_pos, high_index, low_index, input_index));

                nodes_to_outpos.insert(curr_node, curr_pos);
            });

        // println!("Lvl {}: {:?}", l, curr_level);
        level_nodes.push(curr_level);
    }

    // process last level
    //
    // force output node output pos as 0
    {
        let output_node = levels_to_nodes_map.get(&max_level).unwrap();
        assert_eq!(output_node.len(), 1);
        let output_node = output_node.iter().last().unwrap().clone();

        let mut incoming_edges =
            graph.edges_directed(output_node, Incoming).collect_vec();
        incoming_edges.sort_by(|a, b| a.weight().cmp(b.weight()));
        assert!(
            incoming_edges[0].weight() == &0
                && incoming_edges[1].weight() == &1
        );
        let high_node = incoming_edges[1].source();
        let low_node = incoming_edges[0].source();

        let high_index = *nodes_to_outpos.get(&high_node).unwrap();
        let low_index = *nodes_to_outpos.get(&low_node).unwrap();
        let node_weight = graph.node_weight(output_node).unwrap().clone();
        let input_index = translate_node_tag_to_input_index(
            &node_weight,
            input_order,
            alias_map,
        );
        let mut tmp_vec = vec![Node::None; max_width];
        tmp_vec[0] = Node::OpNode(OpNode::new(
            node_weight,
            output_node,
            high_node,
            low_node,
            0,
            high_index,
            low_index,
            input_index,
        ));
        level_nodes.push(tmp_vec);

        nodes_to_outpos.insert(output_node, 0);
    }
    UpDownBDD2::new(level_nodes)
}

struct CodegenUpDownBDD {
    nodes: Vec<OpNode>,
    lvl_bounds: Vec<usize>,
    max_inter_state: usize,
}

impl CodegenUpDownBDD {
    fn new(
        nodes: Vec<OpNode>,
        lvl_bounds: Vec<usize>,
        max_inter_state: usize,
    ) -> Self {
        CodegenUpDownBDD {
            nodes,
            lvl_bounds,
            max_inter_state,
        }
    }
}

#[derive(Clone)]
struct UpDownBDD2 {
    level_nodes: Vec<Vec<Node>>,
}

impl UpDownBDD2 {
    fn new(level_nodes: Vec<Vec<Node>>) -> UpDownBDD2 {
        UpDownBDD2 { level_nodes }
    }
}

#[derive(Clone)]
struct UpDownBDD {
    nodes_levelled: Vec<Vec<OpNode>>,
}

impl Display for UpDownBDD2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "### UpDownBDD ###")?;
        for (index, nodes) in self.level_nodes.iter().enumerate() {
            write!(f, "Level {}: ", index)?;
            for n in nodes {
                write!(f, " {:?} ", n)?;
            }
            writeln!(f, "")?;
        }

        Ok(())
    }
}
impl UpDownBDD {
    fn new(nodes_levelled: Vec<Vec<OpNode>>) -> Self {
        Self { nodes_levelled }
    }

    fn nodes_levelled(&self) -> &[Vec<OpNode>] {
        &self.nodes_levelled
    }

    fn depth(&self) -> usize {
        self.nodes_levelled.len()
    }

    fn total_nodes(&self) -> usize {
        let mut counter = 0;
        for lvl in self.nodes_levelled().iter() {
            counter += lvl.len();
        }
        counter
    }

    fn max_intermediate_storage(&self) -> usize {
        let mut counter = 0;
        for lvl in self.nodes_levelled().iter() {
            for n in lvl {
                counter = std::cmp::max(counter, n.output_pos);
            }
        }
        // minimum 2 for terminal nodes
        std::cmp::max(counter + 1, 2)
    }

    fn to_codegen(&self) -> CodegenUpDownBDD {
        let mut nodes = vec![];
        // starts the boundry at which the i^th level starts
        let mut lvl_bounds = vec![0];
        let mut max_inter_state = 2;

        for lvl_nodes in self.nodes_levelled() {
            nodes.extend_from_slice(lvl_nodes.as_slice());
            lvl_bounds.push(lvl_bounds.last().unwrap() + lvl_nodes.len());

            max_inter_state = std::cmp::max(max_inter_state, lvl_nodes.len());
        }

        lvl_bounds.pop();

        CodegenUpDownBDD::new(nodes, lvl_bounds, max_inter_state)
    }

    fn stats(&self) -> String {
        let mut buffer = String::new();
        buffer.push_str("\n");
        buffer.push_str(&format!("Depth                 = {}\n", self.depth()));
        buffer.push_str(&format!(
            "Total node count      = {}\n",
            self.total_nodes()
        ));
        buffer.push_str(&format!("Node count at depth   = \n"));
        for (index, nodes_lvli) in self.nodes_levelled().iter().enumerate() {
            buffer.push_str(&format!(
                "      depth {} = {}\n",
                index,
                nodes_lvli.len()
            ));
        }
        buffer.push_str("\n");

        return buffer;
    }
}

impl Display for UpDownBDD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "### UpDownBDD ###")?;
        for (index, nodes) in self.nodes_levelled().iter().enumerate() {
            write!(f, "Level {}: ", index)?;
            for n in nodes {
                write!(f, " {} ", n)?;
            }
            writeln!(f, "")?;
        }

        Ok(())
    }
}

struct GGSW {
    bit: bool,
}

impl From<usize> for GGSW {
    fn from(value: usize) -> Self {
        assert!(value <= 1);
        if value == 0 {
            return GGSW { bit: false };
        } else {
            return GGSW { bit: true };
        }
    }
}

impl From<u8> for GGSW {
    fn from(value: u8) -> Self {
        assert!(value <= 1);
        GGSW { bit: value == 1 }
    }
}

#[derive(Clone, Debug, Default)]
struct GLWECt {
    value: usize,
}

impl GLWECt {
    fn new(value: usize) -> GLWECt {
        return GLWECt { value };
    }
}

fn cmux(selector: &GGSW, if_true: &GLWECt, if_false: &GLWECt) -> GLWECt {
    if selector.bit {
        return if_true.clone();
    } else {
        return if_false.clone();
    }
}

fn execute(bdd: &UpDownBDD2, inputs: &[GGSW]) -> GLWECt {
    let mut out = vec![GLWECt::default(); bdd.level_nodes[0].len()];

    out[0] = GLWECt::new(0);
    out[1] = GLWECt::new(1);

    for (lvl_i, lvl_nodes) in bdd.level_nodes.iter().enumerate() {
        let out_old = out.clone();
        for (out_pos, node) in lvl_nodes.iter().enumerate() {
            let out_ct = match node {
                Node::OpNode(node) => cmux(
                    &inputs[node.input_index],
                    &out_old[node.high_index],
                    &out_old[node.low_index],
                ),
                Node::Copy(node) => out_old[out_pos].clone(),
                Node::None => GLWECt::default(),
            };
            out[out_pos] = out_ct;
        }
    }
    out[0].clone()
}

#[derive(Debug, Clone)]
struct CopyNode {
    tag: String,
    parent_node: NodeIndex<u32>,
    node_index: NodeIndex<u32>,
    // output_pos == input_pos
    output_pos: usize,
}

impl CopyNode {
    fn new(
        tag: String,
        parent_node: NodeIndex<u32>,
        node_index: NodeIndex<u32>,
        output_pos: usize,
    ) -> Self {
        Self {
            tag,
            parent_node,
            node_index,
            output_pos,
        }
    }
}

#[derive(Debug, Clone)]
enum Node {
    Copy(CopyNode),
    OpNode(OpNode),
    None,
}

#[derive(Debug, Clone)]
struct OpNode {
    tag: String,
    // Store NodeIndex for debugging purposes
    node_index: NodeIndex<u32>,
    // Debugging purpoess
    high_node: NodeIndex<u32>,
    // Debugging purposes
    low_node: NodeIndex<u32>,
    output_pos: usize,
    high_index: usize,
    low_index: usize,
    input_index: usize,
}

impl OpNode {
    fn new(
        tag: String,
        node_index: NodeIndex<u32>,
        high_node: NodeIndex<u32>,
        low_node: NodeIndex<u32>,
        output_pos: usize,
        high_index: usize,
        low_index: usize,
        input_index: usize,
    ) -> Self {
        Self {
            tag,
            node_index,
            high_node,
            low_node,
            high_index,
            output_pos,
            low_index,
            input_index: input_index,
        }
    }
}

impl Display for OpNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node {{ tag: {}, node_index: {:?}, high_node: {:?}, low_node: {:?}, output_pos: {}, high_index: {}, low_index: {} }}",
            self.tag,
            self.node_index,
            self.high_node,
            self.low_node,
            self.output_pos,
            self.high_index,
            self.low_index
        )
    }
}

fn codegen_multibit_output(udbdds: &[UpDownBDD], out_file: &str) {
    let udbdds = udbdds.iter().map(|b| b.to_codegen()).collect_vec();

    let (v0, v1): (Vec<TokenStream>, Vec<TokenStream>) = udbdds
        .iter()
        .enumerate()
        .map(|(bit_index, ubdd)| {
            let n = ubdd.nodes.len();
            let k = ubdd.lvl_bounds.len();
            (
                parse_str(&format!("B{bit_index}(BitCircuit<{n}, {k}>)"))
                    .unwrap(),
                parse_str(&format!("B{bit_index}")).unwrap(),
            )
        })
        .collect::<Vec<(TokenStream, TokenStream)>>()
        .into_iter()
        .unzip();

    let v3: Vec<TokenStream> = udbdds
        .iter()
        .enumerate()
        .map(|(bit_index, ubdd)| {
            let n = ubdd.nodes.len();
            let k = ubdd.lvl_bounds.len();
            let mut node_buffer = String::new();
            let mut lvl_bounds_buffer = String::new();
            ubdd.nodes.iter().for_each(|node| {
                node_buffer.push_str(&format!(
                    "Node::new({},{},{}),",
                    node.input_index, node.high_index, node.low_index
                ));
            });
            ubdd.lvl_bounds.iter().for_each(|v| {
                lvl_bounds_buffer.push_str(&format!("{v},"));
            });

            parse_str(&format!(
                "AnyBitCircuit::B{}(BitCircuit::new([{}], [{}], {}))",
                bit_index, node_buffer, lvl_bounds_buffer, ubdd.max_inter_state
            ))
            .unwrap()
        })
        .collect();

    let bdd_count = udbdds.len();

    let p2 = quote! {
        pub(crate) enum AnyBitCircuit {
            #(#v0,)*
        }

        impl BitCircuitInfo for AnyBitCircuit {
            fn info(&self) -> (&[Node], &[usize], usize) {
                match self {
                #(
                    AnyBitCircuit::#v1(bit_circuit) => (
                        bit_circuit.nodes.as_ref(),
                        bit_circuit.levels.as_ref(),
                        bit_circuit.max_inter_state
                    ),
                )*
                }
            }
        }

        pub(crate) static OUTPUT_CIRCUITS: Circuit<AnyBitCircuit, #bdd_count> = Circuit (
            [#(#v3,)*]
        );
    };

    let output = quote! {
        use crate::tfhe::bdd_arithmetic::{BitCircuit, BitCircuitInfo, Circuit, Node};

        #p2
    };
    std::fs::write(out_file, output.to_string())
        .expect("Unable to write to file");
}

#[cfg(test)]
mod tests {

    use itertools::Itertools;
    use rand::{Rng, RngCore, rng};

    use crate::pc_update;

    use super::*;

    fn input_bits_to_bdd_var_input(
        input_order: &[String],
        bdd_input_order: &[String],
        bdd_input_alias: Option<&HashMap<String, String>>,
        input_bits: &[u8],
    ) -> Vec<bool> {
        // assert!(input_order.len() == bdd_input_order.len());
        assert!(input_order.len() == input_bits.len());

        let mut bdd_input = vec![false; bdd_input_order.len()];
        bdd_input_order
            .iter()
            .enumerate()
            .for_each(|(bdd_idx, bdd_var)| {
                let dealias = bdd_input_alias
                    .as_deref()
                    .and_then(|m| m.get(bdd_var).cloned())
                    .unwrap_or(bdd_var.clone());
                let pos =
                    input_order.iter().position(|var| var == &dealias).unwrap();
                assert!(input_bits[pos] <= 1);
                bdd_input[bdd_idx] = input_bits[pos] == 1;
            });
        return bdd_input;
    }

    fn u32_to_bits(v: u32) -> Vec<u8> {
        (0..u32::BITS)
            .into_iter()
            .map(|i| ((v >> i) & 1) as u8)
            .collect()
    }

    fn bits_to_u32(bits: &[u8]) -> u32 {
        assert!(bits.len() <= 32);
        bits.iter().enumerate().fold(0u32, |acc, (i, b)| {
            assert!(*b == 0 || *b == 1);
            acc + ((*b as u32) << i) as u32
        })
    }

    #[derive(Debug)]
    enum PCU_T {
        NONE,
        BEQ,
        BNE,
        BLT,
        BGE,
        BLTU,
        BGEU,
        JAL,
        JALR,
    }

    struct PCU {
        op_type: PCU_T,
        // registers
        rs1: u32,
        rs2: u32,
        // program counter
        pc: u32,
        // 20 bit immediate
        imm: u32,
    }

    impl PCU {
        const NONE: PCU = PCU::new(PCU_T::NONE);

        const BEQ: PCU = PCU::new(PCU_T::BEQ);
        const BNE: PCU = PCU::new(PCU_T::BNE);

        const BLT: PCU = PCU::new(PCU_T::BLT);
        const BGE: PCU = PCU::new(PCU_T::BGE);

        const BLTU: PCU = PCU::new(PCU_T::BLTU);
        const BGEU: PCU = PCU::new(PCU_T::BGEU);

        const JAL: PCU = PCU::new(PCU_T::JAL);
        const JALR: PCU = PCU::new(PCU_T::JALR);

        const fn new(op_type: PCU_T) -> Self {
            Self {
                op_type,
                rs1: 0,
                rs2: 0,
                pc: 0,
                imm: 0,
            }
        }

        fn u_rs1(mut self, rs1: u32) -> Self {
            self.rs1 = rs1;
            self
        }

        fn u_rs2(mut self, rs2: u32) -> Self {
            self.rs2 = rs2;
            self
        }

        fn u_pc(mut self, pc: u32) -> Self {
            self.pc = pc;
            self
        }

        fn u_imm(mut self, imm: u32) -> Self {
            let imm = imm & ((1 << 20) - 1);
            self.imm = imm;
            self
        }

        fn set_rs2_equal_rs1(mut self) -> Self {
            self.rs2 = self.rs1;
            self
        }

        fn set_rs1_lt_rs2(mut self) -> Self {
            if self.rs1 == self.rs2 {
                self.rs1 += 1;
            }
            let tmp = self.rs2;
            self.rs2 = std::cmp::max(self.rs1, self.rs2);
            self.rs1 = std::cmp::min(tmp, self.rs1);
            self
        }

        fn set_rs1_gte_rs2(mut self) -> Self {
            let tmp = self.rs2;
            self.rs2 = std::cmp::min(self.rs1, self.rs2);
            self.rs1 = std::cmp::max(tmp, self.rs1);
            self
        }

        fn set_rs1_lt_rs2_signed(mut self) -> Self {
            if self.rs1 == self.rs2 {
                self.rs1 += 1;
            }
            let tmp = self.rs2 as i32;
            self.rs2 = std::cmp::max(self.rs1 as i32, self.rs2 as i32) as u32;
            self.rs1 = std::cmp::min(tmp, self.rs1 as i32) as u32;
            self
        }

        fn set_rs1_gte_rs2_signed(mut self) -> Self {
            let tmp = self.rs2 as i32;
            self.rs2 = std::cmp::min(self.rs1 as i32, self.rs2 as i32) as u32;
            self.rs1 = std::cmp::max(tmp, self.rs1 as i32) as u32;
            self
        }

        fn bdd_encoded_input(&self) -> Vec<u8> {
            // NOOP :   1000
            //
            // JAL  :   1100
            // JALR :   1110
            //
            // BNE  :   0010
            // BEQ  :   0000
            //
            // BLT  :   0110
            // BGE  :   0111
            //
            // BLTU :   0100
            // BGEU :   0101

            let (s0, s1, s2, s3) = match self.op_type {
                PCU_T::NONE => (1, 0, 0, 0),
                PCU_T::JAL => (1, 1, 0, 0),
                PCU_T::JALR => (1, 1, 1, 0),
                PCU_T::BNE => (0, 0, 1, 0),
                PCU_T::BEQ => (0, 0, 0, 0),
                PCU_T::BLT => (0, 1, 1, 0),
                PCU_T::BGE => (0, 1, 1, 1),
                PCU_T::BLTU => (0, 1, 0, 0),
                PCU_T::BGEU => (0, 1, 0, 1),
            };

            let mut input = vec![];
            input.push(s0);
            input.push(s1);
            input.push(s2);
            input.push(s3);

            input.extend(u32_to_bits(self.rs1).iter());
            input.extend(u32_to_bits(self.rs2).iter());

            input.extend(u32_to_bits(self.pc).iter());
            input.extend(u32_to_bits(self.imm).iter().take(20));

            input
        }

        fn expected_update(&self) -> u32 {
            let se_imm = sign_extend(self.imm, 20);
            let default_case = self.pc + 4;
            match self.op_type {
                PCU_T::NONE => default_case,
                PCU_T::BEQ => {
                    if self.rs1 == self.rs2 {
                        self.pc.wrapping_add(se_imm)
                    } else {
                        default_case
                    }
                }
                PCU_T::BNE => {
                    if self.rs1 != self.rs2 {
                        self.pc.wrapping_add(se_imm)
                    } else {
                        default_case
                    }
                }
                PCU_T::BLT => {
                    if (self.rs1 as i32) < self.rs2 as i32 {
                        self.pc.wrapping_add(se_imm)
                    } else {
                        default_case
                    }
                }
                PCU_T::BLTU => {
                    if self.rs1 < self.rs2 {
                        self.pc.wrapping_add(se_imm)
                    } else {
                        default_case
                    }
                }
                PCU_T::BGE => {
                    if (self.rs1 as i32) >= (self.rs2 as i32) {
                        self.pc.wrapping_add(se_imm)
                    } else {
                        default_case
                    }
                }
                PCU_T::BGEU => {
                    if self.rs1 >= self.rs2 {
                        self.pc.wrapping_add(se_imm)
                    } else {
                        default_case
                    }
                }
                PCU_T::JAL => self.pc.wrapping_add(se_imm),
                PCU_T::JALR => (self.pc.wrapping_add(se_imm).wrapping_shr(1))
                    .wrapping_shl(1),
            }
        }
    }

    fn sign_extend(value: u32, bitlen: usize) -> u32 {
        assert!((value >> bitlen) == 0);
        let msb = (value >> (bitlen - 1)) & 1;
        let mut out_v = value;
        for i in bitlen..32 {
            out_v += msb << i;
        }
        return out_v;
    }

    #[test]
    fn trial() {
        let bits = 32;
        let (bdd, vars) = add(bits);
        let bdd_input_order = vars.variable_names();
        let (input_order) = adder_input_order(bits);
        let udbdds = bdd
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &vars, &input_order, None))
            .collect_vec();

        let a = 22131;
        let b = 21412;

        let input_bitstring = u32_to_bits(a)
            .into_iter()
            .take(bits)
            .chain(u32_to_bits(b).into_iter().take(bits))
            .collect_vec();
        let input_ggsw =
            input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

        let out = udbdds
            .iter()
            .map(|ubd| execute(ubd, &input_ggsw).value as u8)
            .collect_vec();

        let have = bits_to_u32(&out);

        assert_eq!(have, a + b);

        // let mut levelised_graph = graph.clone();
        // let levels = levels_for_graph(&levelised_graph);
        // levelise_graph(&mut levelised_graph, levels);
        //
        // println!("Graph: {:?}", Dot::with_config(&graph, &[]));
        // println!(
        //     "Levelised Graph: {:?}",
        //     Dot::with_config(&levelised_graph, &[])
        // );
    }

    #[test]
    fn test_pc_update() {
        let (bdd, vars) = pc_update();
        let bdd_input_order = vars.variable_names();
        let (input_order, input_alias_map) = pc_update_input_order();
        let udbdds = bdd
            .iter()
            .map(|b| {
                updown_bdd_from_bdd(
                    b,
                    &vars,
                    &input_order,
                    Some(&input_alias_map),
                )
            })
            .collect_vec();

        for _ in 0..1000 {
            [
                PCU::BEQ.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs2_equal_rs1(),
                PCU::BEQ.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_lt_rs2(),

                PCU::BNE.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_lt_rs2(),
                PCU::BNE.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs2_equal_rs1(),

                PCU::BLTU.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_lt_rs2(),
                PCU::BLTU.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_gte_rs2(),

                PCU::BGEU.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_gte_rs2(),
                PCU::BGEU.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_lt_rs2(),

                PCU::BLT.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_lt_rs2_signed(),
                PCU::BLT.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_gte_rs2_signed(),

                PCU::BGE.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_gte_rs2_signed(),
                PCU::BGE.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()).set_rs1_lt_rs2_signed(),

                PCU::JAL.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()),
                PCU::JALR.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()),

                PCU::NONE.u_pc(rng().next_u32()).u_imm(rng().next_u32()).u_rs1(rng().next_u32()).u_rs2(rng().next_u32()),

             ].iter_mut().for_each(|pcu| {
                    let input_bitstring = pcu.bdd_encoded_input();

                    let bdd_input =
                        input_bits_to_bdd_var_input(&input_order, &bdd_input_order, Some(&input_alias_map),&input_bitstring);
                    let bdd_out: Vec<u8> = bdd
                        .iter()
                        .map(|bdd| bdd.eval_in(&BddValuation::new(bdd_input.clone())) as u8)
                        .collect();

                    let input_ggsw = input_bitstring.iter().map(|bit| GGSW::from(*bit)).collect_vec();
                    let output_ggsw =udbdds.iter().map(|udb| execute(udb, &input_ggsw).value as u8) .collect_vec();

                    let have_ggsw =bits_to_u32(&output_ggsw);
                    let have_bdd= bits_to_u32(&bdd_out);
                    let want = pcu.expected_update();

                    if have_bdd != have_ggsw {
                        println!("Udbdd output {:#b} != bdd output {:#b}", have_ggsw, have_bdd);
                    }

                    assert_eq!(
                        have_bdd, want,
                        "Failed for Op={:?}, have={:#32b}, want={:#32b}, pc={:#32b}, imm={:#32b}, rs1={:#32b}, rs2={:#32b}",
                        pcu.op_type, have_bdd, want, pcu.pc, sign_extend(pcu.imm, 20), pcu.rs1, pcu.rs2

                    );
        });
        }
    }

    #[test]
    fn test_add_and_sub() {
        // TODO: (jay) tests will fail for bits!=32 because add operation is defined as wrapping,
        // not mod (1<<bits)
        let bits = 32;

        let (add_bdds, add_vars) = add(bits);
        let add_bdd_input_order = add_vars.variable_names();
        let add_input_order = adder_input_order(bits);
        // let udbdd =
        //     updown_bdd_from_bdd(&add_bdds[1], &add_vars, &add_input_order);
        // println!("{}", udbdd);
        let add_udbdds = add_bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &add_vars, &add_input_order, None))
            .collect_vec();

        let (sub_bdds, sub_vars) = sub(bits);
        let sub_bdd_input_order = sub_vars.variable_names();
        let sub_input_order = adder_input_order(bits);
        let sub_udbdds = sub_bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &sub_vars, &sub_input_order, None))
            .collect_vec();

        // println!(
        //     "Add: {}",
        //     add_bdds[bits - 1].to_dot_string(&add_vars, false)
        // );
        // println!("Add: Stats: {}", add_udbdds[bits - 1].stats());
        // println!(
        //     "Sub: {}",
        //     sub_bdds[bits - 1].to_dot_string(&add_vars, false)
        // );
        // println!("Sub: Stats: {}", sub_udbdds[bits - 1].stats());

        // codegen_multibit_output(&add_udbdds, "target/add_codegen.rs");
        // codegen_multibit_output(&sub_udbdds, "target/sub_codegen.rs");

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
                .map(|udb| execute(udb, &input_ggsw).value as u8)
                .collect_vec();
            let sub_out_ggsw = sub_udbdds
                .iter()
                .map(|udb| execute(udb, &input_ggsw).value as u8)
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

        // println!("Unsigned UpDownBDD stats: {}", unsigned_udbdd.stats());
        // println!("Signed UpDownBDD stats: {}", signed_udbdd.stats());
        //
        // codegen_multibit_output(
        //     &[unsigned_udbdd.clone()],
        //     "target/sltu_codegen.rs",
        // );
        // codegen_multibit_output(
        //     &[signed_udbdd.clone()],
        //     "target/slt_codegen.rs",
        // );
        //
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
            let input_bools: Vec<bool> = input_bits_to_bdd_var_input(
                &input_order,
                &bdd_var_order,
                None,
                &input_bits,
            );
            let inputs: Vec<GGSW> =
                input_bits.iter().map(|b| GGSW::from(*b as usize)).collect();

            let uc = a < b;
            let ic = uint_to_int(a, bits) < uint_to_int(b, bits);

            let unsigned_bdd_out =
                unsigned_bdd.eval_in(&BddValuation::new(input_bools.clone()));
            let signed_bdd_out =
                signed_bdd.eval_in(&BddValuation::new(input_bools));
            let unsigned_out = execute(&unsigned_udbdd, &inputs);
            let signed_out = execute(&signed_udbdd, &inputs);

            assert_eq!(unsigned_out.value == 1, unsigned_bdd_out);
            assert_eq!(signed_out.value == 1, signed_bdd_out);
            assert_eq!(
                uc,
                unsigned_out.value == 1,
                "expected {uc} but got {} for a={a} > b={b}",
                unsigned_out.value == 1
            );
            // if a == (1 << (bits - 1)) && b == (1 << (bits - 1)) {
            assert_eq!(
                ic,
                signed_out.value == 1,
                "expected {ic} but got {} for a={a} > b={b}",
                signed_out.value == 1
            )
        }
    }

    #[test]
    fn test_bitwise_ops() {
        let bits = 32;
        let (and_bdd, and_vars) = bitwise_circuit(bits, BIT_OP::AND);
        let (or_bdd, or_vars) = bitwise_circuit(bits, BIT_OP::OR);
        let (xor_bdd, xor_vars) = bitwise_circuit(bits, BIT_OP::XOR);
        let bitwise_input_order = bitwise_circuit_input_order(bits);

        println!("Input order: {:?}", &bitwise_input_order);

        let and_udbdds = and_bdd
            .iter()
            .map(|bdd| {
                updown_bdd_from_bdd(bdd, &and_vars, &bitwise_input_order, None)
            })
            .collect_vec();
        let or_udbdds = or_bdd
            .iter()
            .map(|bdd| {
                updown_bdd_from_bdd(bdd, &and_vars, &bitwise_input_order, None)
            })
            .collect_vec();
        let xor_udbdds = xor_bdd
            .iter()
            .map(|bdd| {
                updown_bdd_from_bdd(bdd, &and_vars, &bitwise_input_order, None)
            })
            .collect_vec();

        // println!("And UpDownBDD stats: {}", and_udbdds[bits - 1].stats());
        // println!("Or UpDownBDD stats: {}", or_udbdds[bits - 1].stats());
        // println!("Xor UpDownBDD stats: {}", xor_udbdds[bits - 1].stats());
        //
        // codegen_multibit_output(&and_udbdds, "target/and_codegen.rs");
        // codegen_multibit_output(&or_udbdds, "target/or_codegen.rs");
        // codegen_multibit_output(&xor_udbdds, "target/xor_codegen.rs");
        // let input_order = unsigned_comparitor_input_order(bits);
        // let bdd_var_order = unsigned_comparitor_bdd_variable_order(bits);
        //
        // for a in 0..1usize << std::cmp::min(10, bits) {
        //     for b in 0..1usize << std::cmp::min(10, bits) {
        //         let input_bits: Vec<u8> = [a, b]
        //             .iter()
        //             .flat_map(|v| (0..bits).map(|e| ((*v >> e) & 1) as u8))
        //             .collect();
        //
        //         let or_c = a.bitor(b)
        //         let and_c = a.bitand(b);
        //         let xor_c = a.bitxor(b);
        //
        //         let and_outs: Vec<GLWECt> =
        //             and_udbdds.iter().map(|bdd| execute(bdd, &inputs)).collect();
        //
        //         (0..bits).for_each(|i| {
        //             assert_eq!(
        //                 (and_c >> i) & 1,
        //                 and_outs[i].value,
        //                 "expected {or_c} but got {} for a={a} > b={b}",
        //                 and_outs[i].value == 1
        //             );
        //         });
        //     }
        // }
    }

    #[test]
    fn test_shift_ops() {
        let bits = 32;
        let shift_bits = 5;

        for op_type in [ShiftOp::SLL, ShiftOp::SRL, ShiftOp::SRA] {
            let (bdds, vars) = shift_circuit(bits, shift_bits, op_type);

            let index_most_expensive = match op_type {
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
                        &shift_circuit_input_order(bits, shift_bits),
                        None,
                    )
                })
                .collect_vec();
            // println!("{}", udbdds[index_most_expensive].stats());
            // udbdds.iter().for_each(|udbb| {
            //     println!("{}", udbb.stats());
            // });

            // codegen_multibit_output(
            //     &udbdds,
            //     &format!("target/{}_codegen.rs", op_type),
            // );

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
                            execute(ubdd, &inputs_bool_ubdds).value == 1
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

    fn uint_to_int(v: u32, bits: usize) -> i32 {
        if bits == 32 {
            return v as i32;
        } else {
            if v < (1 << (bits - 1)) {
                return v as i32;
            } else {
                return -(((1 << bits) - v) as i32);
            }
        }
    }

    fn bit_mask(bits: usize) -> u32 {
        if bits == 32 {
            u32::MAX
        } else {
            (1u32 << bits) - 1
        }
    }

    //TODO: (jay) tests for combined circuits that are not needed at the moment.
    //
    // #[test]
    // fn test_comparitors_combined() {
    //     let bits = 32;
    //     let (bdd, vars) = combined_comparitor_circuit(bits);
    //     println!("{}", bdd.to_dot_string(&vars, false));
    //
    //     let input_order: Vec<String> = vec!["s".to_string()]
    //         .into_iter()
    //         .chain(
    //             (0..bits)
    //                 .map(|i| format!("a{}", i))
    //                 .chain((0..bits).map(|i| format!("b{}", i))),
    //         )
    //         .collect();
    //
    //     let udbdd = updown_bdd_from_bdd(&bdd, &vars, &input_order);
    //     // println!("Stats = {}", udbdd.stats());
    // }
    //
    // #[test]
    // fn test_shifts_combined() {
    //     let bits = 32;
    //     let shift_bits = 5;
    //     let (bdds, vars) = shift_circuit_combined(bits, shift_bits);
    //     // let input_order = shift_circuit_combined_input_order(bits, shift_bits);
    //     // let udbdds = bdds.iter().map(|b| updown_bdd_from_bdd(b, &vars, &input_order)).collect_vec();
    //     println!("{}", bdds[bits - 1].to_dot_string(&vars, false));
    //
    //     for (op_type, (s0, s1)) in [
    //         (ShiftOp::SLL, (0, 0)),
    //         (ShiftOp::SRL, (0, 1)),
    //         (ShiftOp::SRA, (1, 1)),
    //     ] {
    //         for value in rng().random_iter::<u32>().take(1000) {
    //             for shift in 0..1 << shift_bits {
    //                 let inputs_bool: Vec<bool> = (0..shift_bits)
    //                     .map(|i| (shift >> i) & 1 == 1)
    //                     .chain(vec![s0 == 1, s1 == 1].into_iter())
    //                     .chain((0..bits).map(|i| (value >> i) & 1 == 1))
    //                     .collect();
    //                 // println!("Input={:?}", &inputs_bool);
    //
    //                 let out_bdd: Vec<bool> = bdds
    //                     .iter()
    //                     .map(|bdd| {
    //                         bdd.eval_in(&BddValuation::new(inputs_bool.clone()))
    //                     })
    //                     .collect();
    //                 // println!("Out {:?}", &out_bdd.len());
    //                 let have_out = out_bdd
    //                     .iter()
    //                     .enumerate()
    //                     .fold(0u32, |res, (index, b)| {
    //                         res + ((*b as u32) << index)
    //                     });
    //
    //                 let want_out = match op_type {
    //                     ShiftOp::SLL => value << shift,
    //                     ShiftOp::SRL => value >> shift,
    //                     ShiftOp::SRA => ((value as i32) >> (shift)) as u32,
    //                 };
    //
    //                 assert_eq!(
    //                     have_out, want_out,
    //                     "Failed at {:#32b} {:?} {shift}. have_out={:#32b}, want_out={:#32b}",
    //                     value, op_type, have_out, want_out
    //                 );
    //             }
    //         }
    //     }
    // }
    // #[test]
    // fn test_add_sub() {
    //     let bits = 32;
    //     let (bdds, vars) = add_sub(bits);
    //     let bdd_input_order = vars.variable_names();
    //     let input_order = add_sub_input_order(bits);
    //     let udbdds = bdds
    //         .iter()
    //         .map(|b| updown_bdd_from_bdd(b, &vars, &input_order))
    //         .collect_vec();
    //
    //     println!("{}", bdds[bits - 1].to_dot_string(&vars, false));
    //     println!("Stats: {}", udbdds[bits - 1].stats());
    //
    //     let bit_mask = bit_mask(bits);
    //
    //     for _ in 0..100 {
    //         let a = rng().next_u32() & bit_mask;
    //         let b = rng().next_u32() & bit_mask;
    //
    //         [0u8, 1].iter().for_each(|s| {
    //             let input_bitstring = vec![*s]
    //                 .into_iter()
    //                 .chain(u32_to_bits(a).into_iter())
    //                 .chain(u32_to_bits(b))
    //                 .collect_vec();
    //             let input_ggsw = input_bitstring
    //                 .iter()
    //                 .map(|b| GGSW::from(*b))
    //                 .collect_vec();
    //
    //             let out_ggsw = udbdds
    //                 .iter()
    //                 .map(|udb| execute(udb, &input_ggsw).value as u8)
    //                 .collect_vec();
    //
    //             let have_ggsw = bits_to_u32(&out_ggsw);
    //             let want = if *s == 0 {
    //                 a.wrapping_add(b)
    //             } else {
    //                 a.wrapping_sub(b)
    //             };
    //
    //             assert_eq!(want, have_ggsw);
    //         });
    //     }
    // }
}
