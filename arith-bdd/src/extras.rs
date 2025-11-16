// Extras contains circuits for
// 1. JAL/R ( pc+4 )
// 2. AIUPC ( pc + (imm << 12) )
// 3. LUI ( imm << 12)

use biodivine_lib_bdd::*;
use itertools::Itertools;
use proc_macro2::TokenStream;

use crate::{codegen::codegen_multibit_output, graph::updown_bdd_from_bdd};

fn identity_input_order(bits: usize) -> Vec<String> {
    (0..bits).map(|i| format!("x_{}", i)).collect()
}

fn identity(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr = (0..bits).map(|i| format!("x_{}", i)).collect_vec();
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);

    // identity
    let mut out = vec![];
    for i in 0..32 {
        out.push(vars.mk_var_by_name(&format!("x_{}", i)));
    }
    (out, vars)
}

fn ram_offset_input_order() -> Vec<String> {
    let bits = 32;
    (0..bits)
        .map(|i| format!("rs{}", i))
        .chain((0..bits).map(|i| format!("imm{}", i)))
        .collect()
}

/// rs + imm - offset
///
/// offset is a constant
fn ram_address_offset(ram_offset: u32) -> (Vec<Bdd>, BddVariableSet) {
    let neg_ram_offset = ram_offset
        .wrapping_neg()
        .to_le_bytes()
        .iter()
        .flat_map(|v| (0..8).map(move |i| (v >> i & 1) == 1))
        .collect_vec();

    // println!(
    //     "RAM OFFSET: {:?} {:?}",
    //     ram_offset.wrapping_neg().to_le_bytes(),
    //     &neg_ram_offset
    // );

    let vars_arr: Vec<String> = (0..32)
        .flat_map(|i| [format!("rs{}", i), format!("imm{}", i)])
        .collect();
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let mut a = vec![];
    let mut b = vec![];
    (0..32).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("rs{}", i)));
        b.push(vars.mk_var_by_name(&format!("imm{}", i)));
    });

    let mut out = vec![];
    // rs+imm
    {
        // Half adder
        // c_in = 0
        out.push(a[0].xor(&b[0]));
        let mut c = a[0].and(&b[0]);

        for i in 1..32 {
            // full adder
            let s = (a[i].xor(&b[i])).xor(&c);
            out.push(s);
            c = (a[i].and(&b[i])).or(&(a[i].xor(&b[i])).and(&c));
        }
    }
    // Another adder
    // (rs+imm)-ram_offset
    {
        let mut c = vars.mk_false();
        if neg_ram_offset[0] {
            out[0] = out[0].not();
            c = out[0].clone();
        }

        for i in 1..32 {
            // full adder
            if neg_ram_offset[i] {
                let tmp = out[i].clone();
                out[i] = (tmp.not()).xor(&c);
                c = tmp.or(&(tmp.not()).and(&c));
            } else {
                let tmp = out[i].clone();
                out[i] = tmp.xor(&c);
                c = tmp.and(&c);
            }
        }
    }

    (out, vars)
}

fn aiupc_input_order() -> Vec<String> {
    (0..32)
        .map(|i| format!("pc{}", i))
        .chain((0..32).map(|i| format!("imm{}", i)))
        .collect()
}

// PC + (IMM << 12)
fn aiupc() -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = (12..32)
        .flat_map(|i| [format!("pc{}", i), format!("imm{}", i - 12)])
        .chain((0..12).map(|i| format!("pc{}", i)))
        .collect();

    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let mut pc = vec![];
    let mut imm = vec![];
    (0..32).for_each(|i| {
        pc.push(vars.mk_var_by_name(&format!("pc{}", i)));
        if i < 20 {
            imm.push(vars.mk_var_by_name(&format!("imm{}", i)));
        }
    });

    // Copy over LSB 12 bits of PC
    let mut out = vec![];
    (0..12).for_each(|i| {
        out.push(pc[i].clone());
    });

    // Half adder starts at index 12
    // c_in = 0
    out.push(pc[12].xor(&imm[0]));
    let mut c = pc[12].and(&imm[0]);

    for i in 13..32 {
        // full adder
        let s = (pc[i].xor(&imm[i - 12])).xor(&c);
        out.push(s);
        c = (pc[i].and(&imm[i - 12])).or(&(pc[i].xor(&imm[i - 12])).and(&c));
    }

    (out, vars)
}

/// PC + 4
fn jalr() -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr = (0..32).map(|i| format!("pc{}", i)).collect_vec();
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);

    let mut pc = vec![];
    (0..32).for_each(|i| {
        pc.push(vars.mk_var_by_name(&format!("pc{}", i)));
    });

    // PC + 4
    let mut out = vec![pc[0].clone(), pc[1].clone(), pc[2].not()];
    let mut c = pc[2].clone();
    for i in 3..32 {
        // full adder
        let s = pc[i].xor(&c);
        out.push(s);
        c = pc[i].and(&c);
    }

    (out, vars)
}

fn jalr_input_order() -> Vec<String> {
    (0..32).map(|i| format!("pc{}", i)).collect()
}

fn lui_input_order() -> Vec<String> {
    (0..32).map(|i| format!("imm{}", i)).collect()
}

// IMM << 12
fn lui() -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = (0..20).map(|i| format!("imm{}", i)).collect();

    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let mut imm = vec![];
    (0..20).for_each(|i| {
        imm.push(vars.mk_var_by_name(&format!("imm{}", i)));
    });

    // first 12 bits are zero
    let mut out = vec![];
    (0..12).for_each(|_| {
        out.push(vars.mk_false());
    });

    // copy over imm[0..20]
    (12..32).for_each(|i| {
        out.push(imm[i - 12].clone());
    });

    (out, vars)
}

fn codegen_generic<F, F1>(op_fn: F, input_order_fn: F1) -> TokenStream
where
    F: FnOnce() -> (Vec<Bdd>, BddVariableSet),
    F1: FnOnce() -> Vec<String>,
{
    let (bdds, vars) = op_fn();
    let input_order = input_order_fn();
    let udbdds = bdds
        .iter()
        .map(|bdd| updown_bdd_from_bdd(bdd, &vars, &input_order, None))
        .collect_vec();

    codegen_multibit_output(input_order.len(), bdds.len(), &udbdds)
}

pub fn codegen_aiupc() -> TokenStream {
    codegen_generic(aiupc, aiupc_input_order)
}

pub fn codegen_jalr() -> TokenStream {
    codegen_generic(jalr, jalr_input_order)
}

pub fn codegen_lui() -> TokenStream {
    codegen_generic(lui, lui_input_order)
}

pub fn codegen_ram_address_offset(ram_offset: u32) -> TokenStream {
    codegen_generic(|| ram_address_offset(ram_offset), ram_offset_input_order)
}

pub fn codegen_identity(bits: usize) -> TokenStream {
    codegen_generic(|| identity(bits), || identity_input_order(bits))
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use rand::{RngCore, rng};

    use crate::{
        extras::{
            aiupc, aiupc_input_order, identity, identity_input_order, jalr,
            jalr_input_order, lui, lui_input_order, ram_address_offset,
            ram_offset_input_order,
        },
        graph::updown_bdd_from_bdd,
        tests::{GGSW, bits_to_u32, execute, u32_to_bits},
    };

    #[test]
    fn test_aiupc() {
        let (bdds, vars) = aiupc();
        let input_order = aiupc_input_order();
        let udbdds = bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &vars, &input_order, None))
            .collect_vec();

        // println!("AIUPC: Stats for bit 31:\n{}", udbdds[31].stats());

        for _ in 0..1000 {
            let pc = rng().next_u32();
            let imm = rng().next_u32();

            let input_bitstring = u32_to_bits(pc)
                .into_iter()
                .chain(u32_to_bits(imm).into_iter())
                .collect_vec();
            let input_ggsw =
                input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

            let out_ggsw = udbdds
                .iter()
                .map(|ud| execute(ud, &input_ggsw).value() as u8)
                .collect_vec();
            let have = bits_to_u32(&out_ggsw);
            let want = pc.wrapping_add(imm << 12);
            assert_eq!(have, want);
        }
    }

    #[test]
    fn test_jalr() {
        let (bdds, vars) = jalr();
        let input_order = jalr_input_order();
        let udbdds = bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &vars, &input_order, None))
            .collect_vec();

        // println!("JAL(R): Stats for bit 31:\n{}", udbdds[31].stats());

        for _ in 0..1000 {
            let pc = rng().next_u32();

            let input_bitstring = u32_to_bits(pc).into_iter().collect_vec();
            let input_ggsw =
                input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

            let out_ggsw = udbdds
                .iter()
                .map(|ud| execute(ud, &input_ggsw).value() as u8)
                .collect_vec();
            let have = bits_to_u32(&out_ggsw);
            let want = pc.wrapping_add(4);
            assert_eq!(have, want);
        }
    }

    #[test]
    fn test_lui() {
        let (bdds, vars) = lui();
        let input_order = lui_input_order();
        let udbdds = bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &vars, &input_order, None))
            .collect_vec();

        // println!("LUI: Stats for bit 31:\n{}", udbdds[31].stats());

        for _ in 0..1000 {
            let imm = rng().next_u32();

            let input_bitstring = u32_to_bits(imm).into_iter().collect_vec();
            let input_ggsw =
                input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

            let out_ggsw = udbdds
                .iter()
                .map(|ud| execute(ud, &input_ggsw).value() as u8)
                .collect_vec();
            let have = bits_to_u32(&out_ggsw);
            let want = imm.wrapping_shl(12);
            assert_eq!(
                have, want,
                "have={:#32b}, want={:#32b}; imm={:#b}",
                have, want, imm
            );
        }
    }

    #[test]
    fn test_ram_address_offset() {
        let ram_offset = 1 << 18;
        let (bdds, vars) = ram_address_offset(ram_offset);
        let input_order = ram_offset_input_order();
        let udbdds = bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &vars, &input_order, None))
            .collect_vec();

        // println!(
        //     "RAM_ADDRESS_OFFSET: Stats for bit 31:\n{}",
        //     udbdds[31].stats()
        // );

        for _ in 0..1000 {
            let rs = rng().next_u32();
            let imm = rng().next_u32();

            let input_bitstring = u32_to_bits(rs)
                .into_iter()
                .chain(u32_to_bits(imm).into_iter())
                .collect_vec();
            let input_ggsw =
                input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

            let out_ggsw = udbdds
                .iter()
                .map(|udb| execute(udb, &input_ggsw).value() as u8)
                .collect_vec();

            let have_ggsw = bits_to_u32(&out_ggsw);
            let want = rs.wrapping_add(imm).wrapping_sub(ram_offset);

            assert_eq!(
                want, have_ggsw,
                "want={:b}, have={:b}",
                want, have_ggsw
            );
        }
    }

    #[test]
    fn test_identity() {
        let bits = 32;
        let (bdds, vars) = identity(bits);
        let input_order = identity_input_order(bits);
        let udbdds = bdds
            .iter()
            .map(|b| updown_bdd_from_bdd(b, &vars, &input_order, None))
            .collect_vec();

        // println!(
        //     "IDENTITY: Stats for bit {}:\n{}",
        //     bits - 1,
        //     udbdds[bits - 1].stats()
        // );

        for _ in 0..1000 {
            let x = rng().next_u32();

            let input_bitstring = u32_to_bits(x);
            let input_ggsw =
                input_bitstring.iter().map(|b| GGSW::from(*b)).collect_vec();

            let out_ggsw = udbdds
                .iter()
                .map(|udb| execute(udb, &input_ggsw).value() as u8)
                .collect_vec();

            let have_ggsw = bits_to_u32(&out_ggsw);
            let want = x;

            assert_eq!(
                want, have_ggsw,
                "want={:b}, have={:b}",
                want, have_ggsw
            );
        }
    }
}
