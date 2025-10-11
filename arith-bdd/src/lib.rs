pub mod arithmetic;
pub mod bitwise;
pub mod codegen;
pub mod comparitor;
pub mod graph;
pub mod pc_update;
pub mod shift;

pub use arithmetic::*;
pub use bitwise::*;
pub use comparitor::*;
pub use pc_update::*;
pub use shift::*;

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

#[cfg(test)]
mod tests {

    use crate::graph::{Node, UpdownBDD};
    use std::collections::HashMap;

    pub(crate) fn input_bits_to_bdd_var_input(
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

    pub(crate) fn u32_to_bits(v: u32) -> Vec<u8> {
        (0..u32::BITS)
            .into_iter()
            .map(|i| ((v >> i) & 1) as u8)
            .collect()
    }

    pub(crate) fn bits_to_u32(bits: &[u8]) -> u32 {
        assert!(bits.len() <= 32);
        bits.iter().enumerate().fold(0u32, |acc, (i, b)| {
            assert!(*b == 0 || *b == 1);
            acc + ((*b as u32) << i) as u32
        })
    }

    pub(crate) fn sign_extend(value: u32, bitlen: usize) -> u32 {
        assert!((value >> bitlen) == 0);
        let msb = (value >> (bitlen - 1)) & 1;
        let mut out_v = value;
        for i in bitlen..32 {
            out_v += msb << i;
        }
        return out_v;
    }

    pub(crate) struct GGSW {
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
    pub(crate) struct GLWECt {
        value: usize,
    }

    impl GLWECt {
        fn new(value: usize) -> GLWECt {
            return GLWECt { value };
        }

        pub(crate) fn value(&self) -> usize {
            self.value
        }
    }

    fn cmux(selector: &GGSW, if_true: &GLWECt, if_false: &GLWECt) -> GLWECt {
        if selector.bit {
            return if_true.clone();
        } else {
            return if_false.clone();
        }
    }

    pub(crate) fn execute(bdd: &UpdownBDD, inputs: &[GGSW]) -> GLWECt {
        let mut out = vec![GLWECt::default(); bdd.max_width()];

        out[0] = GLWECt::new(0);
        out[1] = GLWECt::new(1);

        for (_lvl_i, lvl_nodes) in bdd.level_nodes().iter().enumerate() {
            let out_old = out.clone();
            for (out_pos, node) in lvl_nodes.iter().enumerate() {
                let out_ct = match node {
                    Node::OpNode(node) => cmux(
                        &inputs[node.input_index()],
                        &out_old[node.high_index()],
                        &out_old[node.low_index()],
                    ),
                    Node::Copy(_node) => out_old[out_pos].clone(),
                    Node::None => GLWECt::default(),
                };
                out[out_pos] = out_ct;
            }
        }
        out[0].clone()
    }

    pub(crate) fn uint_to_int(v: u32, bits: usize) -> i32 {
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

    pub(crate) fn bit_mask(bits: usize) -> u32 {
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
