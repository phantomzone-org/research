use std::collections::HashMap;
use std::fmt;
// use petgraph::dot::dot_parser::
use biodivine_lib_bdd::*;
use petgraph::Graph;
use petgraph::algo::toposort;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};
use proc_macro2::TokenStream;
use quote::quote;
use std::fs::write;
use syn::parse_str;

fn unsigned_comparitor(bits: usize) -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars_arr: Vec<String> = unsigned_comparitor_bdd_variable_order(bits);
    let vars_arr_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_arr_ref);
    let mut a = vec![];
    let mut b = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b.push(vars.mk_var_by_name(&format!("b{}", i)));
    });

    let mut comp = a[bits - 1].and(&b[bits - 1].not());
    let mut not_casc = (a[bits - 1].xor(&b[bits - 1])).not();

    for i in (0..bits - 1).rev() {
        comp = comp.or(&(a[i].and(&b[i].not())).and(&not_casc));
        not_casc = not_casc.and(&(a[i].xor(&b[i])).not());
    }

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
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect()
}

// Note: variables that are used together must be placed next to each other in variable array. This is because width of the resulting BDD depends on variable
// ordering. If variables that are used together are placed far apart in the ordering, the resulting BDD is very wide. In fact the width at haldway through
// the depth doubles with every bit.
//
// This is why we prefer criss cross input bit order: a0 b0 a1 b1... and not a0 a1 ... a{n-1} b0 b1 ....
//
// TODO: Variable ordering determines BDD. What's the optimal variable ordering per circuit, heuristically?
fn add(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = unsigned_add_bdd_variable_order(bits);
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

fn unsigned_add_input_order(bits: usize) -> Vec<String> {
    (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect()
}

fn unsigned_add_bdd_variable_order(bits: usize) -> Vec<String> {
    (0..bits)
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect()
}

fn levels_for_graph(graph: &Graph<&str, i32>) -> HashMap<NodeIndex, usize> {
    let top_sort = toposort(graph, Default::default()).unwrap();

    let mut level_map = HashMap::new();

    for i in 0..top_sort.len() {
        let mut level = 0;
        for incoming_edge in graph.edges_directed(top_sort[i], petgraph::Direction::Incoming) {
            let pred = incoming_edge.source();
            level = std::cmp::max(level, *level_map.get(&pred).unwrap() + 1);
        }
        assert!(level_map.insert(top_sort[i], level).is_none())
    }

    level_map
}

fn updown_bdd_from_bdd(bdd: &Bdd, vars: &BddVariableSet, input_order: &[String]) -> UpDownBDD {
    let var_names = vars.variable_names();
    if var_names.len() != (bdd.num_vars() as usize) {
        panic!(
            "Bdd is incompatible with the variable set ({} vs. {} variables)",
            bdd.num_vars(),
            var_names.len()
        );
    }

    // BDD upside down
    let mut graph = DiGraph::new();
    // Bdd pointer index -> NodeIndex
    let mut bdd_index_to_node_index = HashMap::new();
    let terminal_node0 = graph.add_node("0");
    let terminal_node1 = graph.add_node("1");
    bdd_index_to_node_index.insert(0, terminal_node0);
    bdd_index_to_node_index.insert(1, terminal_node1);
    // bdd.pointers().take(2).for_each(f);
    for node_pointer in bdd.pointers().skip(2) {
        // bdd's index must not repeat
        assert!(
            bdd_index_to_node_index
                .insert(
                    node_pointer.0,
                    graph.add_node(&var_names[bdd.var_of(node_pointer).0 as usize]),
                )
                .is_none()
        );
    }
    for node_pointer in bdd.pointers().skip(2) {
        let curr_node = bdd_index_to_node_index.get(&node_pointer.0).unwrap();

        let high_link = bdd.high_link_of(node_pointer);
        let high_node = bdd_index_to_node_index.get(&high_link.0).unwrap();
        // directed edge from high link node to curr node
        graph.add_edge(*high_node, *curr_node, 1);

        let low_link = bdd.low_link_of(node_pointer);
        let low_node = bdd_index_to_node_index.get(&low_link.0).unwrap();
        // directed edge from low link node to curr node
        graph.add_edge(*low_node, *curr_node, 0);
    }

    // let dot = Dot::with_config(&graph, &[]).to_string();
    // println!("{}", dot);

    // create upside BDD repr. for our purposes
    let node_index_to_lvl = levels_for_graph(&graph);
    // println!("Node levels = {:?}", node_index_to_lvl);

    // Level boundaries
    let mut level_bounds = vec![2];
    // Nodes stored sorted by level in a contiguous array.
    // Boundary between levels are defined in level_bounds. For ex, level_bounds[0] is index before which nodes of level 0 end and first node of level 1 exists.
    let mut nodes_lvld = vec![
        Node::new("0".to_string(), None, None),
        Node::new("1".to_string(), None, None),
    ];
    let mut tmp_node_index_to_index = HashMap::new();
    tmp_node_index_to_index.insert(terminal_node0, 0);
    tmp_node_index_to_index.insert(terminal_node1, 1);
    let mut curr_index = 2;
    for level in 1..node_index_to_lvl.values().max().unwrap() + 1 {
        for (k, v) in node_index_to_lvl.iter() {
            // filter out nodes at level
            if level == *v {
                let high_index = graph
                    .edges_directed(*k, petgraph::Direction::Incoming)
                    .find(|e| *e.weight() == 1)
                    .map(|e| *tmp_node_index_to_index.get(&e.source()).unwrap());
                let low_index = graph
                    .edges_directed(*k, petgraph::Direction::Incoming)
                    .find(|e| *e.weight() == 0)
                    .map(|e| *tmp_node_index_to_index.get(&e.source()).unwrap());
                let tag = *graph.node_weight(*k).unwrap();
                assert!(high_index.is_some());
                assert!(low_index.is_some());

                nodes_lvld.push(Node::new(tag.to_string(), high_index, low_index));
                tmp_node_index_to_index.insert(*k, curr_index);

                curr_index += 1;
            }
        }
        level_bounds.push(curr_index);
    }

    // Set node's input index as per input order
    //
    // GGSW selector ciphertext for node[j] is stored at input[node[j].input_index]
    nodes_lvld.iter_mut().skip(2).for_each(|node| {
        node.input_index = input_order.iter().position(|t| &node.tag == t).unwrap();
    });

    return UpDownBDD::new(nodes_lvld, level_bounds);
}

struct UpDownBDD {
    nodes_levelled: Vec<Node>,
    level_boundaries: Vec<usize>,
}

impl UpDownBDD {
    fn new(nodes_levelled: Vec<Node>, level_boundaries: Vec<usize>) -> Self {
        Self {
            nodes_levelled,
            level_boundaries,
        }
    }

    fn nodes_levelled(&self) -> &[Node] {
        &self.nodes_levelled
    }

    fn depth(&self) -> usize {
        self.level_boundaries.len() - 1
    }

    fn stats(&self) -> String {
        let mut buffer = String::new();
        buffer.push_str("\n");
        buffer.push_str(&format!("Depth                 = {}\n", self.depth()));
        buffer.push_str(&format!(
            "Total node count      = {}\n",
            self.nodes_levelled.len() - 2
        ));
        buffer.push_str(&format!("Node count at depth   = \n"));
        for i in 0..self.level_boundaries.len() - 1 {
            buffer.push_str(&format!(
                "      depth {} = {}\n",
                i + 1,
                self.level_boundaries[i + 1] - self.level_boundaries[i]
            ));
        }
        buffer.push_str("\n");

        return buffer;
    }

    fn print(&self) -> String {
        let mut buffer = String::new();
        buffer.push_str("[");
        self.nodes_levelled().iter().for_each(|node| {
            buffer.push_str(&format!(
                "Node::new({},{},{}),",
                node.input_index,
                node.high_index.unwrap_or_default(),
                node.high_index.unwrap_or_default()
            ));
        });
        buffer.push_str("]");

        buffer
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

#[derive(Clone, Debug)]
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

fn execute(bdd: &UpDownBDD, inputs: &[GGSW]) -> GLWECt {
    let mut out = vec![GLWECt::new(0), GLWECt::new(1)];

    let lvl_bounds = &bdd.level_boundaries;
    // starts at level 1
    for i in 0..lvl_bounds.len() - 1 {
        let start = lvl_bounds[i];
        let end = lvl_bounds[i + 1];
        for j in start..end {
            let node = &bdd.nodes_levelled[j];
            out.push(cmux(
                &inputs[node.input_index],
                &out[node.high_index.unwrap()],
                &out[node.low_index.unwrap()],
            ));
        }
    }

    out[out.len() - 1].clone()
}

#[derive(Debug)]
struct Node {
    tag: String,
    high_index: Option<usize>,
    low_index: Option<usize>,
    input_index: usize,
}

impl Node {
    fn new(tag: String, high_index: Option<usize>, low_index: Option<usize>) -> Self {
        // Node is either root or not
        assert!(
            (high_index.is_none() && low_index.is_none())
                || (high_index.is_some() && low_index.is_some())
        );
        Self {
            tag,
            high_index,
            low_index,
            input_index: 0,
        }
    }

    fn is_root(&self) -> bool {
        self.high_index.is_none() && self.low_index.is_none()
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Node {{ tag: {}, high_index: {:?}, low_index: {:?} }}",
            self.tag, self.high_index, self.low_index
        )
    }
}

fn codegen_multibit_output(udbdds: &[UpDownBDD], out_file: &str) {
    let p1 = quote! {
        pub(super) struct Node {
            input_index: usize,
            high_index: usize,
            low_index: usize,
        }

        impl Node {
            const fn new(input_index: usize, high_index: usize, low_index: usize) -> Self {
                Self {
                    input_index,
                    high_index,
                    low_index,
                }
            }
        }

        pub(super) struct BitCircuit<const N: usize, const K: usize> {
            lvld_nodes: [Node; N],
            lvl_bounds: [usize; K],
        }

        impl<const N: usize, const K: usize> BitCircuit<N, K> {
            const fn new(lvld_nodes: [Node; N], lvl_bounds: [usize; K]) -> Self {
                Self {
                    lvld_nodes,
                    lvl_bounds,
                }
            }
        }
    };

    let (v0, v1): (Vec<TokenStream>, Vec<TokenStream>) = udbdds
        .iter()
        .map(|bdd| {
            let n = bdd.nodes_levelled().len();
            let k = bdd.level_boundaries.len();

            (
                parse_str(&format!("C{n}x{k}(BitCircuit<{n}, {k}>)")).unwrap(),
                parse_str(&format!("C{n}x{k}")).unwrap(),
            )
        })
        .collect::<Vec<(TokenStream, TokenStream)>>()
        .into_iter()
        .unzip();

    let v3: Vec<TokenStream> = udbdds
        .iter()
        .map(|bdd| {
            let n = bdd.nodes_levelled().len();
            let k = bdd.level_boundaries.len();
            let mut node_buffer = String::new();
            let mut lvl_bounds_buffer = String::new();
            bdd.nodes_levelled().iter().for_each(|node| {
                node_buffer.push_str(&format!(
                    "Node::new({},{},{}),",
                    node.input_index,
                    node.high_index.unwrap_or_default(),
                    node.low_index.unwrap_or_default()
                ));
            });
            bdd.level_boundaries.iter().for_each(|v| {
                lvl_bounds_buffer.push_str(&format!("{v},"));
            });

            parse_str(&format!(
                "AnyBitCircuit::C{n}x{k}(BitCircuit::new([{}], [{}]))",
                node_buffer, lvl_bounds_buffer
            ))
            .unwrap()
        })
        .collect();

    let bdd_count = udbdds.len();

    let p2 = quote! {
        pub(super) enum AnyBitCircuit {
            #(#v0,)*
        }

        impl AnyBitCircuit {
            pub(super) fn inner(&self) -> (&[Node], &[usize]) {
                match self {
                #(
                    AnyBitCircuit::#v1(bit_circuit) => (
                        bit_circuit.lvld_nodes.as_ref(),
                        bit_circuit.lvl_bounds.as_ref(),
                    ),
                )*
                }
            }
        }

        static OUTPUT_CIRCUITS: [AnyBitCircuit; #bdd_count] = [#(#v3,)*];
    };

    let output = quote! {
        #p1
        #p2
    };

    write(out_file, output.to_string()).expect("Unable to write to file");
}
#[cfg(test)]
mod tests {

    use super::*;

    fn input_bits_to_bdd_var_input(
        input_order: &[String],
        bdd_input_order: &[String],
        input_bits: &[u8],
    ) -> Vec<bool> {
        assert!(input_order.len() == bdd_input_order.len());
        assert!(input_order.len() == input_bits.len());

        let mut bdd_input = vec![false; input_order.len()];
        bdd_input_order
            .iter()
            .enumerate()
            .for_each(|(bdd_idx, bdd_var)| {
                let pos = input_order.iter().position(|var| var == bdd_var).unwrap();
                assert!(input_bits[pos] <= 1);
                bdd_input[bdd_idx] = input_bits[pos] == 1;
            });
        return bdd_input;
    }

    #[test]
    fn test_add() {
        let bits = 32;
        let (summands, vars) = add(bits);

        let si_updown_bdd: Vec<UpDownBDD> = summands
            .iter()
            .map(|si_bdd| updown_bdd_from_bdd(si_bdd, &vars, &unsigned_add_input_order(bits)))
            .collect();

        codegen_multibit_output(&si_updown_bdd, "./target/add.rs");

        // println!("Si last stats: {}", si_updown_bdd[bits - 1].stats());
        // println!("{:?}", si_updown_bdd.node_tags());

        let input_order = unsigned_add_input_order(bits);
        let bdd_var_order = unsigned_add_bdd_variable_order(bits);

        for a in 0..1usize << std::cmp::min(10, bits) {
            for b in 0..1 << std::cmp::min(10, bits) {
                let input_bits: Vec<u8> = [a, b]
                    .iter()
                    .flat_map(|v| (0..bits).map(|e| ((*v >> e) & 1) as u8))
                    .collect();
                let input_bools =
                    input_bits_to_bdd_var_input(&input_order, &bdd_var_order, &input_bits);
                let inputs: Vec<GGSW> =
                    input_bits.iter().map(|b| GGSW::from(*b as usize)).collect();

                let c = (a + b) % (1 << bits);

                for j in 0..bits {
                    let cj_bit = (c >> j) & 1;

                    let j_bdd_out = summands[j].eval_in(&BddValuation::new(input_bools.clone()));
                    let j_out = execute(&si_updown_bdd[j], &inputs);

                    assert_eq!(
                        cj_bit, j_out.value,
                        "expected {cj_bit} but got {} for {j}^th bit of a={a} + b={b}",
                        j_out.value
                    );
                    assert_eq!(j_bdd_out as usize, j_out.value);
                }
            }
        }
    }

    #[test]
    fn test_unsigned_comparitor() {
        let bits = 10;
        let (comp_bdd, vars) = unsigned_comparitor(bits);

        // println!("{}", actual_bdd.to_dot_string(&var_names, false));
        let comp_udbdd =
            updown_bdd_from_bdd(&comp_bdd, &vars, &unsigned_comparitor_input_order(bits));
        let unsigned_comparator_input_order = unsigned_comparitor_input_order(bits);
        let unsigned_comparator_bdd_var_order = unsigned_comparitor_bdd_variable_order(bits);

        println!("Comp UpDownBDD stats: {}", comp_udbdd.stats());

        for a in 0..1usize << std::cmp::min(10, bits) {
            for b in 0..1usize << std::cmp::min(10, bits) {
                let input_bits: Vec<u8> = [a, b]
                    .iter()
                    .flat_map(|v| (0..bits).map(|e| ((*v >> e) & 1) as u8))
                    .collect();
                let input_bools: Vec<bool> = input_bits_to_bdd_var_input(
                    &unsigned_comparator_input_order,
                    &unsigned_comparator_bdd_var_order,
                    &input_bits,
                );
                let inputs: Vec<GGSW> =
                    input_bits.iter().map(|b| GGSW::from(*b as usize)).collect();

                let c = a > b;

                let bdd_out = comp_bdd.eval_in(&BddValuation::new(input_bools));
                let out = execute(&comp_udbdd, &inputs);

                assert_eq!(out.value == 1, bdd_out);
                assert_eq!(
                    c,
                    out.value == 1,
                    "expected {c} but got {} for a={a} > b={b}",
                    out.value == 1
                );
            }
        }
    }
}
