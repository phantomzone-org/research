use core::{
    FourierGLWESecret, GGLWECiphertext, GGSWCiphertext, GLWEAutomorphismKey, GLWECiphertext,
    GLWEOps, GLWEPacker, GLWEPlaintext, GLWESecret, Infos, ScratchOwned,
    backend::{Backend, Decoding, Encoding, FFT64, Module, ScalarZnx, Stats, ZnxViewMut},
    glwe,
};
use std::collections::HashMap;

use itertools::{Itertools, izip};
use num_bigfloat::BigFloat;
use rand::{RngCore, rng};
use sampling::source::{self, Source};

const SIGMA: f64 = 3.2;

fn random_data_in_mod(logn: usize, k_pt: usize, source: &mut Source) -> Vec<i64> {
    (0..1 << logn)
        .into_iter()
        .map(|_| uint_to_i64(source.next_u64n((1 << k_pt), (1 << k_pt) - 1), 1 << k_pt))
        .collect_vec()
}

fn add_vec_i64(o: &mut [i64], a: &[i64], b: &[i64], k_pt: usize) {
    assert_eq!(o.len(), a.len());
    assert_eq!(b.len(), a.len());
    izip!(o.iter_mut(), a.iter(), b.iter()).for_each(|(o0, a0, b0)| {
        *o0 = ((a0.wrapping_shl(i64::BITS - k_pt as u32))
            .wrapping_add(b0.wrapping_shl(i64::BITS - k_pt as u32)))
        .wrapping_shr(i64::BITS - k_pt as u32);
    });
}

fn case1() {
    let basek = 20;
    let logn = 4;
    let rank = 1;
    let module = Module::<FFT64>::new(1 << logn);

    let mut seed = [0; 32];
    rng().fill_bytes(&mut seed);
    let mut source = Source::new(seed);

    let mut sk = GLWESecret::alloc(&module, rank);
    sk.fill_binary_prob(0.5, &mut source);
    let sk_fourier = FourierGLWESecret::from(&module, &sk);

    let mut scratch_owned = ScratchOwned::new(GLWECiphertext::encrypt_sk_scratch_space(
        &module,
        basek,
        basek * 10,
    ));

    // GLWE encrypt
    let k_pt = 4;
    let data1 = random_data_in_mod(logn, k_pt, &mut source);
    let mut pt1 = GLWEPlaintext::alloc(&module, basek, k_pt);
    pt1.data.encode_vec_i64(0, basek, k_pt, &data1, k_pt);
    let mut glwe1 = GLWECiphertext::alloc(&module, basek, basek * 3, rank);
    glwe1.encrypt_sk(
        &module,
        &pt1,
        &sk_fourier,
        &mut source.branch(),
        &mut source.branch(),
        SIGMA,
        scratch_owned.borrow(),
    );

    {
        let mut pt_tmp = GLWEPlaintext::alloc(&module, basek, glwe1.k());
        glwe1.decrypt(&module, &mut pt_tmp, &sk_fourier, scratch_owned.borrow());
        pt_tmp.sub_inplace_ab(&module, &pt1);
        println!("glwe1 noise = {}", pt_tmp.data.std(0, basek).log2());
    }

    let data2 = random_data_in_mod(logn, k_pt, &mut source);
    let mut pt2 = GLWEPlaintext::alloc(&module, basek, k_pt);
    pt2.data.encode_vec_i64(0, basek, k_pt, &data2, k_pt);
    let mut glwe2 = GLWECiphertext::alloc(&module, basek, basek * 2, rank);
    glwe2.encrypt_sk(
        &module,
        &pt2,
        &sk_fourier,
        &mut source.branch(),
        &mut source.branch(),
        SIGMA,
        scratch_owned.borrow(),
    );

    // GLWE Add
    let mut data12 = vec![0; 1 << logn];
    add_vec_i64(&mut data12, &data1, &data2, k_pt);
    let mut glwe21 = GLWECiphertext::alloc(&module, basek, glwe1.k(), glwe1.rank());
    glwe21.add(&module, &glwe2, &glwe1);

    // Measure noise
    let mut pt_want = GLWEPlaintext::alloc(&module, basek, k_pt);
    pt_want.data.encode_vec_i64(0, basek, k_pt, &data12, k_pt);

    let mut pt_have = GLWEPlaintext::alloc(&module, basek, glwe21.k());
    glwe21.decrypt(&module, &mut pt_have, &sk_fourier, scratch_owned.borrow());

    pt_have.sub_inplace_ab(&module, &pt_want);
    println!("glwe21 noise = {}", pt_have.data.std(0, basek).log2());
}

fn case2() {
    let basek = 20;
    let logn = 12;
    let rank = 1;
    let module = Module::<FFT64>::new(1 << logn);

    let mut seed = [0; 32];
    rng().fill_bytes(&mut seed);
    let mut source = Source::new(seed);

    let mut sk = GLWESecret::alloc(&module, rank);
    sk.fill_binary_prob(0.5, &mut source);
    let sk_fourier = FourierGLWESecret::from(&module, &sk);

    let k_glwe1 = basek * 3;
    let k_ggsw = basek * 5;
    let digits_ggsw = 1;

    let mut scratch_own = ScratchOwned::new(
        GLWECiphertext::encrypt_sk_scratch_space(&module, basek, k_glwe1)
            | GLWECiphertext::decrypt_scratch_space(&module, basek, k_glwe1)
            | GLWECiphertext::decrypt_scratch_space(&module, basek, k_glwe1)
            | GGSWCiphertext::encrypt_sk_scratch_space(&module, basek, k_ggsw, rank)
            | GLWECiphertext::external_product_scratch_space(
                &module,
                basek,
                k_glwe1,
                k_glwe1,
                k_ggsw,
                digits_ggsw,
                rank,
            ),
    );

    // GLWE1
    let k_pt = 4;
    let data1 = random_data_in_mod(logn, k_pt, &mut source);
    let mut pt1 = GLWEPlaintext::alloc(&module, basek, k_pt);
    pt1.data.encode_vec_i64(0, basek, k_pt, &data1, k_pt);
    let mut glwe1 = GLWECiphertext::alloc(&module, basek, k_glwe1, rank);
    glwe1.encrypt_sk(
        &module,
        &pt1,
        &sk_fourier,
        &mut source.branch(),
        &mut source.branch(),
        SIGMA,
        scratch_own.borrow(),
    );

    // GGSW1
    let mut ggsw1 = GGSWCiphertext::alloc(&module, basek, k_ggsw, glwe1.size(), digits_ggsw, rank);
    let mut pt2 = ScalarZnx::<Vec<u8>>::new(module.n(), 1);
    pt2.raw_mut()[0] = 1;
    ggsw1.encrypt_sk(
        &module,
        &pt2,
        &sk_fourier,
        &mut source.branch(),
        &mut source.branch(),
        SIGMA,
        scratch_own.borrow(),
    );

    // External product: GLWE2 = GLWE1 x GGSW1
    let mut glwe2 = GLWECiphertext::alloc(&module, basek, glwe1.k(), rank);
    glwe2.external_product(&module, &glwe1, &ggsw1, scratch_own.borrow());

    // Measure noise
    {
        let mut pt_tmp = GLWEPlaintext::alloc(&module, basek, glwe2.k());
        glwe2.decrypt(&module, &mut pt_tmp, &sk_fourier, scratch_own.borrow());
        pt_tmp.sub_inplace_ab(&module, &pt1);
        println!("glwe2 noise = {}", pt_tmp.data.std(0, basek).log2());
    }

    // GGSW2
    let mut ggsw2 = GGSWCiphertext::alloc(&module, basek, k_ggsw, glwe2.size(), digits_ggsw, rank);
    let mut pt3 = ScalarZnx::<Vec<u8>>::new(module.n(), 1);
    pt3.raw_mut()[0] = 0;
    ggsw2.encrypt_sk(
        &module,
        &pt3,
        &sk_fourier,
        &mut source.branch(),
        &mut source.branch(),
        SIGMA,
        scratch_own.borrow(),
    );

    // External product GLWE2 x GGSW2
    let mut glwe3 = GLWECiphertext::alloc(&module, basek, glwe2.k(), rank);
    glwe3.external_product(&module, &glwe2, &ggsw2, scratch_own.borrow());

    // Measure noise
    {
        // Want all zeros
        let mut pt_tmp = GLWEPlaintext::alloc(&module, basek, glwe3.k());
        glwe3.decrypt(&module, &mut pt_tmp, &sk_fourier, scratch_own.borrow());
        println!("glwe3 noise = {}", pt_tmp.data.std(0, basek).log2());
    }
}

fn packing() {
    let basek = 20;
    let logn = 5;
    let rank = 1;
    let module = Module::<FFT64>::new(1 << logn);
    let k_glwe = basek * 3;
    let k_gglwe = basek * 4;
    let digits_gglwe = 1;
    const SIGMA: f64 = 3.2;

    let mut scratch_owned = ScratchOwned::new(
        GLWEAutomorphismKey::generate_from_sk_scratch_space(&module, basek, k_gglwe, rank)
            | GLWEPacker::scratch_space(&module, basek, k_glwe, k_gglwe, digits_gglwe, rank)
            | GLWECiphertext::decrypt_scratch_space(&module, basek, k_glwe)
            | GLWECiphertext::encrypt_sk_scratch_space(&module, basek, k_glwe),
    );

    let mut seed = [0; 32];
    rng().fill_bytes(&mut seed);
    let mut source = Source::new(seed);

    let mut sk = GLWESecret::alloc(&module, rank);
    sk.fill_binary_prob(0.5, &mut source);
    let sk_fourier = FourierGLWESecret::from(&module, &sk);

    let log_batch = 4;

    let k_pt = logn;
    let multiples = (0..1 << log_batch)
        .map(|i| i * (module.n() >> log_batch))
        .collect_vec();
    let glwes = (0..module.n() >> log_batch)
        .map(|i| {
            let mut data = vec![0; module.n()];
            multiples.iter().for_each(|index| {
                data[*index] = uint_to_i64(i as u64, 1 << k_pt);
            });
            // data[1 * (module.n() >> log_batch)] = uint_to_i64(i as u64, 1 << k_pt);
            let mut pt = GLWEPlaintext::alloc(&module, basek, k_pt);
            pt.data.encode_vec_i64(0, basek, k_pt, &data, k_pt);
            // println!("data {i}: {:?}", &data);
            // println!("pt   {i}: {:?}", &pt.data);

            let mut glwe1 = GLWECiphertext::alloc(&module, basek, k_glwe, rank);
            glwe1.encrypt_sk(
                &module,
                &pt,
                &sk_fourier,
                &mut source.branch(),
                &mut source.branch(),
                SIGMA,
                scratch_owned.borrow(),
            );
            glwe1
        })
        .collect_vec();

    let mut packer = GLWEPacker::new(&module, log_batch, basek, k_glwe, rank);

    // Generate Auto keys
    let mut auto_keys: HashMap<i64, GLWEAutomorphismKey<Vec<u8>, FFT64>> = HashMap::new();
    let gal_els: Vec<i64> = GLWEPacker::galois_elements(&module);
    gal_els.iter().for_each(|gal_el| {
        let mut key = GLWEAutomorphismKey::alloc(
            &module,
            basek,
            k_gglwe,
            glwes[0].size(),
            digits_gglwe,
            rank,
        );
        key.generate_from_sk(
            &module,
            *gal_el,
            &sk,
            &mut source.branch(),
            &mut source.branch(),
            SIGMA,
            scratch_owned.borrow(),
        );

        auto_keys.insert(*gal_el, key);
    });

    // Pack GLWEs
    glwes.iter().for_each(|ct| {
        packer.add(&module, Some(ct), &auto_keys, scratch_owned.borrow());
    });
    let mut res = GLWECiphertext::alloc(&module, basek, k_glwe, rank);
    packer.flush(&module, &mut res);

    let mut want_data = vec![0; module.n()];
    (0..module.n() >> log_batch).for_each(|i| {
        for k in multiples.iter() {
            want_data[k + reverse_bits(i, (logn - log_batch) as u32)] =
                uint_to_i64(i as u64, 1 << k_pt);
        }
    });
    let mut want_pt = GLWEPlaintext::alloc(&module, basek, k_pt);
    want_pt
        .data
        .encode_vec_i64(0, want_pt.basek(), want_pt.k(), &want_data, want_pt.k());
    println!("PT want = {}", want_pt.data);

    let mut have_pt = GLWEPlaintext::alloc(&module, basek, res.k());
    res.decrypt(&module, &mut have_pt, &sk_fourier, scratch_owned.borrow());
    println!("PT1 = {}", have_pt.data);

    have_pt.sub_inplace_ab(&module, &want_pt);
    println!("Noise = {}", have_pt.data.std(0, basek).log2());
}

fn reverse_bits(v: usize, bits: u32) -> usize {
    v.reverse_bits() >> (usize::BITS - bits)
}

fn main() {
    case1();
    // case2();
    // packing();
    // println!("Hello, world!");
}

fn uint_to_i64(v: u64, modulus: u64) -> i64 {
    let v = v % modulus;
    if v >= modulus / 2 {
        return -((modulus - v) as i64);
    } else {
        return v as i64;
    }
}

fn i64_to_u64(v: i64, modulus: u64) -> u64 {
    if v.is_negative() {
        modulus - v.abs() as u64
    } else {
        v.abs() as u64
    }
}
