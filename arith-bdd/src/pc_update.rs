use std::collections::HashMap;

use biodivine_lib_bdd::*;
use itertools::Itertools;
use proc_macro2::TokenStream;

use crate::{codegen::codegen_multibit_output, graph::updown_bdd_from_bdd};

fn input_order() -> (Vec<String>, HashMap<String, String>) {
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

pub fn codegen_pc_update() -> TokenStream {
    let (bdds, vars) = pc_update();
    let (input_order, input_alias_map) = input_order();
    let udbdds = bdds
        .iter()
        .map(|bdd| {
            updown_bdd_from_bdd(
                bdd,
                &vars,
                &input_order,
                Some(&input_alias_map),
            )
        })
        .collect_vec();

    codegen_multibit_output(input_order.len(), bdds.len(), &udbdds)
}
#[cfg(test)]
mod test {
    use biodivine_lib_bdd::BddValuation;
    use itertools::Itertools;
    use rand::{RngCore, rng};

    use crate::{
        graph::updown_bdd_from_bdd,
        pc_update::{input_order, pc_update},
        tests::{
            GGSW, bits_to_u32, execute, input_bits_to_bdd_var_input,
            sign_extend, u32_to_bits,
        },
    };

    #[allow(non_camel_case_types)]
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

    #[test]
    fn test_pc_update() {
        let (bdd, vars) = pc_update();
        let bdd_input_order = vars.variable_names();
        let (input_order, input_alias_map) = input_order();
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

        // println!("UpDownBDD stats for bit {}: \n{}", 31, udbdds[31].stats());

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
                    let output_ggsw =udbdds.iter().map(|udb| execute(udb, &input_ggsw).value() as u8) .collect_vec();

                    let have_ggsw =bits_to_u32(&output_ggsw);
                    let have_bdd= bits_to_u32(&bdd_out);
                    let want = pcu.expected_update();

                    assert_eq!(have_bdd, have_ggsw,"Udbdd output {:#b} != bdd output {:#b}", have_ggsw, have_bdd);

                    assert_eq!(
                        have_bdd, want,
                        "Failed for Op={:?}, have={:#32b}, want={:#32b}, pc={:#32b}, imm={:#32b}, rs1={:#32b}, rs2={:#32b}",
                        pcu.op_type, have_bdd, want, pcu.pc, sign_extend(pcu.imm, 20), pcu.rs1, pcu.rs2

                    );
        });
        }
    }
}
