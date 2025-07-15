use std::collections::HashMap;
use std::{fmt::Display, iter};
// use petgraph::dot::dot_parser::
use biodivine_lib_bdd::*;
use petgraph::Direction::Outgoing;
use petgraph::Graph;
use petgraph::algo::toposort;
use petgraph::dot::Dot;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};
use proc_macro2::TokenStream;
use quote::quote;
use std::fs::write;
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

/// Input order: s0,s1,..sk,a0,a1...,an
fn shift_circuits_input_order(input_bits: usize, shift_bits: usize) -> Vec<String> {
    (0..shift_bits)
        .map(|i| format!("x_{}", i))
        .chain((0..input_bits).map(|i| format!("x_{}", i + shift_bits)))
        .collect()
}

fn slr(
    input_bits: usize,
    shift_bits: usize,
) -> (
    Vec<biodivine_lib_bdd::Bdd>,
    biodivine_lib_bdd::BddVariableSet,
) {
    let variables = BddVariableSet::new_anonymous((input_bits + shift_bits) as u16);
    let vars = variables.variables();

    let mut a = vec![];
    let mut b = vec![];
    (0..shift_bits).for_each(|i| {
        b.push(variables.mk_var(vars[i]));
    });
    (0..input_bits).for_each(|i| {
        a.push(variables.mk_var(vars[shift_bits + i]));
    });

    for i in 0..shift_bits {
        let jump = 1 << i;

        let a_clone = a.clone();
        for j in 0..input_bits {
            let if_true_var = {
                if jump + j >= input_bits {
                    &variables.mk_false()
                } else {
                    &a_clone[j + jump]
                }
            };
            let if_false_var = &a_clone[j];

            a[j] = Bdd::if_then_else(&b[i], &if_true_var, &if_false_var);
        }
    }
    (a, variables)
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

fn shift_circuit(
    input_bits: usize,
    shift_bits: usize,
    shift_op: ShiftOp,
) -> (
    Vec<biodivine_lib_bdd::Bdd>,
    biodivine_lib_bdd::BddVariableSet,
) {
    let variables = BddVariableSet::new_anonymous((input_bits + shift_bits) as u16);
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

fn xor_circuit() -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars = BddVariableSet::new(&["a", "b"]);
    let mut a = vars.mk_var_by_name("a");
    let mut b = vars.mk_var_by_name("b");

    let c: Bdd = a.xor(&b);

    (c, vars)
}

fn or_circuit() -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars = BddVariableSet::new(&["a", "b"]);
    let mut a = vars.mk_var_by_name("a");
    let mut b = vars.mk_var_by_name("b");

    let c: Bdd = a.or(&b);

    (c, vars)
}

fn and_circuit() -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars = BddVariableSet::new(&["a", "b"]);
    let mut a = vars.mk_var_by_name("a");
    let mut b = vars.mk_var_by_name("b");

    let c: Bdd = a.and(&b);

    (c, vars)
}

fn bitwise_ops_input_order() -> Vec<String> {
    vec![format!("a"), format!("b")]
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

    let comp = comparitor_circuit(&a, &b, bits);
    (comp, vars)
}

fn signed_comparitor(bits: usize) -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars_arr: Vec<String> = unsigned_comparitor_bdd_variable_order(bits);
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
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect()
}

fn sub(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = unsigned_add_bdd_variable_order(bits);
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

fn add_clubbed(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = unsigned_add_clubbed_bdd_variable_order(bits);
    let vars_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_ref);
    let mut a = vec![];
    let mut b0 = vec![];
    let mut b1 = vec![];
    (0..bits).for_each(|i| {
        a.push(vars.mk_var_by_name(&format!("a{}", i)));
        b0.push(vars.mk_var_by_name(&format!("b0{}", i)));
        b1.push(vars.mk_var_by_name(&format!("b1{}", i)))
    });
    let ss = vars.mk_var_by_name(&format!("ss"));

    // Half adder
    // c_in = 0
    let mut out = vec![];
    let b = (ss.and(&b0[0])).or(&(ss.not()).and(&b1[0]));
    out.push(a[0].xor(&b));
    let mut c = a[0].and(&b);

    for i in 1..bits {
        // full adder
        let b = (ss.and(&b0[i])).or(&(ss.not()).and(&b1[i]));
        let s = (a[i].xor(&b)).xor(&c);
        out.push(s);
        c = (a[i].and(&b)).or(&(a[i].xor(&b)).and(&c));
    }

    (out, vars)
}

fn unsigned_add_input_order(bits: usize) -> Vec<String> {
    (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect()
}

fn unsigned_add_clubbed_order(bits: usize) -> Vec<String> {
    let mut v: Vec<String> = (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b0{}", i)))
        .chain((0..bits).map(|i| format!("b1{}", i)))
        .collect();
    v.push(format!("ss"));
    v
}

fn unsigned_add_bdd_variable_order(bits: usize) -> Vec<String> {
    (0..bits)
        .flat_map(|i| [format!("a{}", i), format!("b{}", i)])
        .collect()
}

fn unsigned_add_clubbed_bdd_variable_order(bits: usize) -> Vec<String> {
    let mut v: Vec<String> = (0..bits)
        .flat_map(|i| [format!("a{}", i), format!("b0{}", i), format!("b1{}", i)])
        .collect();
    v.push(format!("ss"));
    v
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

fn trialtrial(bdd: &Bdd, vars: &BddVariableSet) {
    let var_names = vars.variable_names();
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
        graph.add_edge(*curr_node, *high_node, 1);

        let low_link = bdd.low_link_of(node_pointer);
        let low_node = bdd_index_to_node_index.get(&low_link.0).unwrap();
        // directed edge from low link node to curr node
        graph.add_edge(*curr_node, *low_node, 0);
    }

    let node_index_to_lvl = levels_for_graph(&graph);
    let max_lvl = node_index_to_lvl.values().max().unwrap();
    let mut all_unique_nodes = vec![];
    let mut all_non_uni = vec![];
    for lvl in (0..*max_lvl).rev() {
        let mut unique_nodes: Vec<(NodeIndex, Vec<NodeIndex>)> = vec![];

        for (node, _) in node_index_to_lvl.iter().filter(|(_, lvl0)| &lvl == *lvl0) {
            let mut children: Vec<NodeIndex> = graph
                .neighbors_directed(*node, Outgoing)
                .map(|c| c)
                .collect();
            children.sort();
            let mut flag = false;

            for uni_node in unique_nodes.iter() {
                if uni_node.1.as_slice() == children.as_slice() {
                    flag = true
                }
            }

            if !flag {
                unique_nodes.push((*node, children));
            } else {
                all_non_uni.push(*node);
            }
        }
        let mut tmp = vec![];
        unique_nodes.iter().for_each(|node| {
            tmp.push(node.0.clone());
        });

        all_unique_nodes.push(tmp);
    }
    println!("All Unique {:?}", all_unique_nodes);
    println!("All Non Unique {:?}", &all_non_uni);
    for node in all_non_uni {
        graph.remove_node(node);
    }

    let dot = Dot::with_config(&graph, &[]).to_string();
    println!("{}", dot);
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

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node {{ tag: {}, high_index: {:?}, low_index: {:?} }}",
            self.tag, self.high_index, self.low_index
        )
    }
}

fn codegen_singlebit_out(ubdd: &UpDownBDD, out_file: &str) {
    let p1 = quote! {
        use super::super::{BitCircuitInfo, Node};

        pub(crate) struct BitCircuit<const N: usize, const K: usize> {
           pub(crate) lvld_nodes: [Node; N],
           pub(crate) lvl_bounds: [usize; K],
        }

        impl<const N: usize, const K: usize> BitCircuit<N, K> {
            const fn new(lvld_nodes: [Node; N], lvl_bounds: [usize; K]) -> Self {
                Self {
                    lvld_nodes,
                    lvl_bounds,
                }
            }
        }
        impl<const N: usize, const K: usize> BitCircuitInfo for BitCircuit<N, K> {
            fn info(&self) -> (&[Node], &[usize]) {
                (self.lvld_nodes.as_ref(), self.lvl_bounds.as_ref())
            }
        }
    };

    let node_count = ubdd.nodes_levelled().len();
    let lvl_b_count = ubdd.level_boundaries.len();
    let bit_circuit: TokenStream = {
        let mut nodes_buffer = String::new();
        let mut lvl_bounds_buffer = String::new();
        ubdd.nodes_levelled().iter().for_each(|node| {
            nodes_buffer.push_str(&format!(
                "Node::new({},{},{}),",
                node.input_index,
                node.high_index.unwrap_or_default(),
                node.low_index.unwrap_or_default()
            ));
        });
        ubdd.level_boundaries.iter().for_each(|lb| {
            lvl_bounds_buffer.push_str(&format!("{lb},"));
        });

        parse_str(&format!(
            "BitCircuit::new([{}], [{}])",
            nodes_buffer, lvl_bounds_buffer
        ))
        .unwrap()
    };

    let output = quote! {
        #p1

        pub(crate) static OUTPUT_CIRCUIT: BitCircuit<#node_count, #lvl_b_count> = #bit_circuit;
    };

    write(out_file, output.to_string()).expect("Unable to write to file");
}

fn codegen_multibit_output(udbdds: &[UpDownBDD], out_file: &str) {
    let p1 = quote! {
        use super::super::{BitCircuitInfo, Node};

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
        pub(crate) enum AnyBitCircuit {
            #(#v0,)*
        }

        impl BitCircuitInfo for AnyBitCircuit {
            fn info(&self) -> (&[Node], &[usize]) {
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

        pub(crate) static OUTPUT_CIRCUITS: [AnyBitCircuit; #bdd_count] = [#(#v3,)*];
    };

    let output = quote! {
        #p1
        #p2
    };

    write(out_file, output.to_string()).expect("Unable to write to file");
}
#[cfg(test)]
mod tests {

    use std::ops::{BitAnd, BitOr, BitXor};

    use rand::{Rng, rng};

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

    // #[test]
    // fn test_add_clubbed() {
    //     let bits = 5;
    //     let (summands, vars) = add_clubbed(bits);
    //     println!(
    //         "Stats: {}",
    //         updown_bdd_from_bdd(
    //             &summands[bits - 1],
    //             &vars,
    //             &unsigned_add_clubbed_order(bits)
    //         )
    //         .stats()
    //     );
    //     println!("{}", summands[bits - 1].to_dot_string(&vars, false));
    // }

    #[test]
    fn test_add() {
        let bits = 32;
        let (summands, vars) = add(bits);

        println!("{}", summands[bits - 1].to_dot_string(&vars, false));

        let si_updown_bdd: Vec<UpDownBDD> = summands
            .iter()
            .map(|si_bdd| updown_bdd_from_bdd(si_bdd, &vars, &unsigned_add_input_order(bits)))
            .collect();

        codegen_multibit_output(&si_updown_bdd, "./target/add_codegen.rs");

        println!("Si last stats: {}", si_updown_bdd[bits - 1].stats());
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
    fn test_sub() {
        let bits = 32;
        let (summands, vars) = sub(bits);

        println!("{}", summands[bits - 1].to_dot_string(&vars, false));

        let si_updown_bdd: Vec<UpDownBDD> = summands
            .iter()
            .map(|si_bdd| updown_bdd_from_bdd(si_bdd, &vars, &unsigned_add_input_order(bits)))
            .collect();

        codegen_multibit_output(&si_updown_bdd, "./target/sub_codegen.rs");

        println!("Si last stats: {}", si_updown_bdd[bits - 1].stats());
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

                let c = (a.wrapping_sub(b)) % (1 << bits);
                for j in 0..bits {
                    let cj_bit = (c >> j) & 1;

                    let j_bdd_out = summands[j].eval_in(&BddValuation::new(input_bools.clone()));
                    let j_out = execute(&si_updown_bdd[j], &inputs);

                    // println!("BDD eval={j_bdd_out}, Circuit eval={}", j_out.value);

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
    fn test_comparitors() {
        let bits = 10;
        let (unsigned_bdd, unsigned_vars) = unsigned_comparitor(bits);
        let (signed_bdd, signed_vars) = signed_comparitor(bits);

        // println!("{}", actual_bdd.to_dot_string(&var_names, false));
        let unsigned_udbdd = updown_bdd_from_bdd(
            &unsigned_bdd,
            &unsigned_vars,
            &unsigned_comparitor_input_order(bits),
        );
        let signed_udbdd = updown_bdd_from_bdd(
            &signed_bdd,
            &signed_vars,
            &unsigned_comparitor_input_order(bits),
        );

        println!("Unsigned UpDownBDD stats: {}", unsigned_udbdd.stats());
        println!("Signed UpDownBDD stats: {}", signed_udbdd.stats());

        codegen_singlebit_out(&unsigned_udbdd, "target/sltu_codegen.rs");
        codegen_singlebit_out(&signed_udbdd, "target/slt_codegen.rs");

        let input_order = unsigned_comparitor_input_order(bits);
        let bdd_var_order = unsigned_comparitor_bdd_variable_order(bits);

        for a in 0..1usize << std::cmp::min(10, bits) {
            for b in 0..1usize << std::cmp::min(10, bits) {
                let input_bits: Vec<u8> = [a, b]
                    .iter()
                    .flat_map(|v| (0..bits).map(|e| ((*v >> e) & 1) as u8))
                    .collect();
                let input_bools: Vec<bool> =
                    input_bits_to_bdd_var_input(&input_order, &bdd_var_order, &input_bits);
                let inputs: Vec<GGSW> =
                    input_bits.iter().map(|b| GGSW::from(*b as usize)).collect();

                let uc = a < b;
                let ic = uint_to_int(a, bits) < uint_to_int(b, bits);

                let unsigned_bdd_out =
                    unsigned_bdd.eval_in(&BddValuation::new(input_bools.clone()));
                let signed_bdd_out = signed_bdd.eval_in(&BddValuation::new(input_bools));
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
                // }
            }
        }
    }

    #[test]
    fn test_bitwise_ops() {
        let (and_bdd, and_vars) = and_circuit();
        let (or_bdd, or_vars) = or_circuit();
        let (xor_bdd, xor_vars) = xor_circuit();

        let and_udbdd: UpDownBDD =
            updown_bdd_from_bdd(&and_bdd, &and_vars, &bitwise_ops_input_order());
        let or_udbdd = updown_bdd_from_bdd(&or_bdd, &or_vars, &bitwise_ops_input_order());
        let xor_udbdd = updown_bdd_from_bdd(&xor_bdd, &xor_vars, &bitwise_ops_input_order());
        println!("And UpDownBDD stats: {}", and_udbdd.stats());
        println!("Or UpDownBDD stats: {}", or_udbdd.stats());
        println!("Xor UpDownBDD stats: {}", xor_udbdd.stats());

        codegen_singlebit_out(&and_udbdd, "target/and_codegen.rs");
        codegen_singlebit_out(&or_udbdd, "target/or_codegen.rs");
        codegen_singlebit_out(&xor_udbdd, "target/xor_codegen.rs");
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
    fn sll_test() {
        let bits = 32;
        let shift_bits = 5;

        for op_type in [ShiftOp::SLL, ShiftOp::SRL, ShiftOp::SRA] {
            let (bdds, vars) = shift_circuit(bits, shift_bits, op_type);

            // bdds.iter().for_each(|bdd| {
            // println!("{}", bdd.to_dot_string(&vars, false));
            // });

            let udbdds: Vec<UpDownBDD> = bdds
                .iter()
                .map(|bdd| {
                    updown_bdd_from_bdd(bdd, &vars, &shift_circuits_input_order(bits, shift_bits))
                })
                .collect();

            codegen_multibit_output(&udbdds, &format!("target/{}_codegen.rs", op_type));

            // udbdds.iter().for_each(|udbb| {
            //     println!("{}", udbb.stats());
            // });

            for value in rng().random_iter::<u32>().take(1000) {
                for shift in 0..1 << shift_bits {
                    let inputs_bool: Vec<bool> = (0..shift_bits)
                        .map(|i| (shift >> i) & 1 == 1)
                        .chain((0..bits).map(|i| (value >> i) & 1 == 1))
                        .collect();
                    // println!("Input={:?}", &inputs_bool);

                    let out_bdd: Vec<bool> = bdds
                        .iter()
                        .map(|bdd| bdd.eval_in(&BddValuation::new(inputs_bool.clone())))
                        .collect();
                    // println!("Out {:?}", &out_bdd);
                    let have_out = out_bdd
                        .iter()
                        .enumerate()
                        .fold(0u32, |res, (index, b)| res + ((*b as u32) << index));

                    let want_out = match op_type {
                        ShiftOp::SLL => value << shift,
                        ShiftOp::SRL => value >> shift,
                        ShiftOp::SRA => ((value as i32) >> (shift)) as u32,
                    };

                    assert_eq!(
                        have_out, want_out,
                        "Failed at {:#b} {:?} {shift}. have_out={:#b}, want_out={:#b}",
                        value, op_type, have_out, want_out
                    );
                }
            }
        }
    }

    fn uint_to_int(v: usize, bits: usize) -> i64 {
        if v < (1 << (bits - 1)) {
            return v as i64;
        } else {
            return -(((1 << bits) - v) as i64);
        }
    }
}
