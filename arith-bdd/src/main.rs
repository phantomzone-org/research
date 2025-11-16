use arith_bdd::{
    codegen_add, codegen_aiupc, codegen_and, codegen_identity, codegen_jalr,
    codegen_lui, codegen_or, codegen_pc_update, codegen_ram_address_offset,
    codegen_signed_comparitor, codegen_sll, codegen_sra, codegen_srl,
    codegen_sub, codegen_unsigned_comparitor, codegen_xor,
};
use proc_macro2::TokenStream;
use std::fs;
use std::path::Path;
use std::process::Command;

fn generate_and_write(
    token_stream: TokenStream,
    output_filename: &str,
    target_dir: &Path,
) {
    // Write to file
    let output_path = target_dir.join(output_filename);
    fs::write(&output_path, token_stream.to_string())
        .expect(&format!("Failed to write {}", output_filename));

    // Format the file with rustfmt
    let status = Command::new("rustfmt")
        .arg(&output_path)
        .status()
        .expect("Failed to run rustfmt");

    if status.success() {
        println!("Successfully generated and formatted: {:?}", output_path);
    } else {
        eprintln!("rustfmt failed with status: {}", status);
    }
}

fn main() {
    let word_size = 32;

    // Create target/codegen directory if it doesn't exist
    let target_dir = Path::new("target/codegen");
    fs::create_dir_all(target_dir)
        .expect("Failed to create target/codegen directory");

    // Generate shift operations
    generate_and_write(codegen_sll(word_size), "codegen_sll.rs", target_dir);
    generate_and_write(codegen_srl(word_size), "codegen_srl.rs", target_dir);
    generate_and_write(codegen_sra(word_size), "codegen_sra.rs", target_dir);

    // Generate arithmetic operations
    generate_and_write(codegen_add(word_size), "codegen_add.rs", target_dir);
    generate_and_write(codegen_sub(word_size), "codegen_sub.rs", target_dir);

    // Generate bitwise operations
    generate_and_write(codegen_and(word_size), "codegen_and.rs", target_dir);
    generate_and_write(codegen_or(word_size), "codegen_or.rs", target_dir);
    generate_and_write(codegen_xor(word_size), "codegen_xor.rs", target_dir);

    // Generate comparators
    generate_and_write(
        codegen_unsigned_comparitor(word_size),
        "codegen_unsigned_comparitor.rs",
        target_dir,
    );
    generate_and_write(
        codegen_signed_comparitor(word_size),
        "codegen_signed_comparitor.rs",
        target_dir,
    );

    // Generate PC update
    generate_and_write(codegen_pc_update(), "codegen_pc_update.rs", target_dir);

    // Generate AIUPC
    generate_and_write(codegen_aiupc(), "codegen_aiupc.rs", target_dir);

    // Generate LUI
    generate_and_write(codegen_lui(), "codegen_lui.rs", target_dir);

    // Generate AIUPC
    generate_and_write(codegen_jalr(), "codegen_jalr.rs", target_dir);

    // Generate RAM offset circuit for offset 2^18
    generate_and_write(
        codegen_ram_address_offset(2u32.pow(18)),
        "codegen_ram_offset.rs",
        target_dir,
    );

    // Generate identity
    generate_and_write(codegen_identity(32), "codegen_identity.rs", target_dir);
}
