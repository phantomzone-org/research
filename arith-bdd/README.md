# BDD circuits

To codegen arithmetic and binary BDD circuits for arbitrary width inputs, first set word_size parametes in main.rs (i.e. word_size=32). Then execute `cargo run --release`.

The codegen files are available at `target/codegen`.

The codegen circuits are compatible for execution with poulpy FHE library.
