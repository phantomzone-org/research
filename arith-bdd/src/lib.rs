use std::fmt;
use std::{collections::HashMap, ops::Not, str::FromStr};
// use petgraph::dot::dot_parser::
use biodivine_lib_bdd::*;
use petgraph::{
    dot::{Config, Dot},
    graph::{DiGraph, NodeIndex},
    visit::{EdgeRef, NodeRef},
};

fn unsigned_comparitor(bits: usize) -> (biodivine_lib_bdd::Bdd, biodivine_lib_bdd::BddVariableSet) {
    let vars_arr: Vec<String> = (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect();
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

fn add(bits: usize) -> (Vec<Bdd>, BddVariableSet) {
    let vars_arr: Vec<String> = (0..bits)
        .map(|i| format!("a{}", i))
        .chain((0..bits).map(|i| format!("b{}", i)))
        .collect();
    let vars_arr_ref: Vec<&str> = vars_arr.iter().map(|a| a.as_str()).collect();
    let vars = BddVariableSet::new(&vars_arr_ref);
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
        c = (a[i].and(&b[i])).or(&(a[i].xor(&b[i])).and(&c));

        out.push(s);
    }

    (out, vars)
}

fn updown_bdd_from_bdd(bdd: &Bdd, var_names: &[String]) -> UpDownBDD {
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
    let mut node_index_to_lvl = HashMap::new();
    fn dfs(
        curr_node: NodeIndex,
        curr_level: usize,
        level_map: &mut HashMap<NodeIndex, usize>,
        graph: &petgraph::Graph<&str, i32>,
    ) {
        if let Some(existing_lvl) = level_map.get(&curr_node) {
            level_map.insert(curr_node, std::cmp::max(curr_level, *existing_lvl));
        } else {
            level_map.insert(curr_node, curr_level);
        }
        for node in graph.edges_directed(curr_node, petgraph::Direction::Outgoing) {
            dfs(node.target(), curr_level + 1, level_map, graph);
        }
    }
    for r_node in [terminal_node0, terminal_node1] {
        dfs(r_node, 0, &mut node_index_to_lvl, &graph);
    }

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
                    .map(|e| {
                        // if tmp_node_index_to_index.get(&e.source()).is_none() {
                        //     println!("ASS: {:?}", tmp_node_index_to_index);
                        //     println!(
                        //         "Level = {}, Curr node tag = {:?}, Curr node index = {:?}, Missing node tag = {:?}, Missing node index = {:?}",
                        //         level,
                        //         graph.node_weight(*k),
                        //         *k,
                        //         graph.node_weight(e.source()),
                        //         e.source()
                        //     );
                        // }
                        *tmp_node_index_to_index.get(&e.source()).unwrap()
                    });
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

    fn node_tags(&self) -> Vec<String> {
        self.nodes_levelled
            .iter()
            .enumerate()
            .map(|(index, n)| n.tag.clone())
            .collect()
    }

    fn depth(&self) -> usize {
        self.level_boundaries.len() - 1
    }
    // TODO: fn for external product depth, etc.
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

fn execute(bdd: &UpDownBDD, inputs: &[GGSW], input_index_map: &[usize]) -> GLWECt {
    let mut out = vec![GLWECt::new(0), GLWECt::new(1)];

    let lvl_bounds = &bdd.level_boundaries;
    // starts at level 1
    for i in 0..lvl_bounds.len() - 1 {
        let start = lvl_bounds[i];
        let end = lvl_bounds[i + 1];
        for j in start..end {
            let node = &bdd.nodes_levelled[j];
            out.push(cmux(
                &inputs[input_index_map[j]],
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
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let bits = 3;
        let (summands, var_names) = add(bits);

        // println!("{}", actual_bdd.to_dot_string(&var_names, false));

        let si_updown_bdd: Vec<UpDownBDD> = summands
            .iter()
            .map(|si_bdd| updown_bdd_from_bdd(si_bdd, &var_names.variable_names()))
            .collect();
        // println!("{:?}", si_updown_bdd.node_tags());

        let input_variables: Vec<String> = (0..bits)
            .map(|i| format!("a{}", i))
            .chain((0..bits).map(|i| format!("b{}", i)))
            .collect();
        let si_input_index_map: Vec<Vec<usize>> = si_updown_bdd
            .iter()
            .map(|si_udbdd| {
                let node_order = si_udbdd.node_tags();
                // Stores the index at which GGSW ciphertext of j^th node is stored.
                // Note that j=0,1 are terminal nodes and are never accessed
                let mut input_index_map = vec![0, 0];
                node_order.iter().skip(2).for_each(|tag| {
                    let index_in_input = input_variables.iter().position(|t| tag == t).unwrap();
                    input_index_map.push(index_in_input);
                });
                input_index_map
            })
            .collect();

        for a in 0..1usize << bits {
            for b in 0..1 << bits {
                let inputs: Vec<GGSW> = [a, b]
                    .iter()
                    .flat_map::<Vec<GGSW>, _>(|v| {
                        (0..bits).map(|e| GGSW::from((v >> e) & 1)).collect()
                    })
                    .collect();
                let input_bools: Vec<bool> = inputs.iter().map(|c| c.bit).collect();

                let c = (a + b) % (1 << bits);

                for j in 0..bits {
                    let cj_bit = (c >> j) & 1;

                    let j_bdd_out = summands[j].eval_in(&BddValuation::new(input_bools.clone()));
                    let j_out = execute(&si_updown_bdd[j], &inputs, &si_input_index_map[j]);

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
        let bits = 5;
        let (comp_bdd, var_names) = unsigned_comparitor(bits);

        // println!("{}", actual_bdd.to_dot_string(&var_names, false));
        let comp_udbdd = updown_bdd_from_bdd(&comp_bdd, &var_names.variable_names());

        let input_variables: Vec<String> = (0..bits)
            .map(|i| format!("a{}", i))
            .chain((0..bits).map(|i| format!("b{}", i)))
            .collect();
        // Stores the index at which GGSW ciphertext of j^th node is stored.
        // Note that j=0,1 are terminal nodes and are never accessed
        let mut input_index_map = vec![0, 0];
        comp_udbdd.node_tags().iter().skip(2).for_each(|tag| {
            let index_in_input = input_variables.iter().position(|t| tag == t).unwrap();
            input_index_map.push(index_in_input);
        });

        println!("UpDownBDD depth = {}", comp_udbdd.depth());

        for a in 0..1usize << bits {
            for b in 0..1usize << bits {
                let inputs: Vec<GGSW> = [a, b]
                    .iter()
                    .flat_map::<Vec<GGSW>, _>(|v| {
                        (0..bits).map(|e| GGSW::from((v >> e) & 1)).collect()
                    })
                    .collect();
                let input_bools: Vec<bool> = inputs.iter().map(|c| c.bit).collect();

                let c = a > b;

                let bdd_out = comp_bdd.eval_in(&BddValuation::new(input_bools));
                let out = execute(&comp_udbdd, &inputs, &input_index_map);

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
