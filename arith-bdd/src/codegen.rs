use itertools::Itertools;
use proc_macro2::TokenStream;
use quote::quote;
use syn::parse_str;

use crate::graph::{Node, UpdownBDD};

pub(crate) struct CodegenUpDownBDD {
    nodes: Vec<Node>,
    _lvl_bounds: Vec<usize>,
    max_inter_state: usize,
}

impl CodegenUpDownBDD {
    pub(crate) fn new(
        nodes: Vec<Node>,
        lvl_bounds: Vec<usize>,
        max_inter_state: usize,
    ) -> Self {
        CodegenUpDownBDD {
            nodes,
            _lvl_bounds: lvl_bounds,
            max_inter_state,
        }
    }
}

pub(crate) fn codegen_multibit_output(udbdds: &[UpdownBDD]) -> TokenStream {
    let udbdds = udbdds.iter().map(|b| b.to_codegen()).collect_vec();

    let (v0, v1): (Vec<TokenStream>, Vec<TokenStream>) = udbdds
        .iter()
        .enumerate()
        .map(|(bit_index, ubdd)| {
            let n = ubdd.nodes.len();
            // let k = ubdd.lvl_bounds.len();
            (
                parse_str(&format!("B{bit_index}(BitCircuit<{n}>)")).unwrap(),
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
            let mut node_buffer = String::new();
            // let mut lvl_bounds_buffer = String::new();
            ubdd.nodes.iter().for_each(|node| {
                match node {
                    Node::OpNode(node) => node_buffer.push_str(&format!(
                        "Node::Op({},{},{}),",
                        node.input_index(),
                        node.high_index(),
                        node.low_index()
                    )),
                    Node::Copy(_) => {
                        node_buffer.push_str(&format!("Node::Copy,",))
                    }
                    Node::None => {
                        node_buffer.push_str(&format!("Node::None,",))
                    }
                };
            });
            // ubdd.lvl_bounds.iter().for_each(|v| {
            //     lvl_bounds_buffer.push_str(&format!("{v},"));
            // });

            parse_str(&format!(
                "AnyBitCircuit::B{}(BitCircuit::new([{}], {}))",
                bit_index, node_buffer, ubdd.max_inter_state
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

    output
}
