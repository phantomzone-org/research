use biodivine_lib_bdd::*;
use itertools::Itertools;
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::Graph;
use petgraph::algo::toposort;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;

use crate::codegen::CodegenUpDownBDD;

#[derive(Debug, Clone)]
pub(crate) enum Node {
    Copy(CopyNode),
    OpNode(OpNode),
    None,
}

#[derive(Debug, Clone)]
pub(crate) struct CopyNode {
    tag: String,
    parent_node: NodeIndex<u32>,
    node_index: NodeIndex<u32>,
    // output_pos == input_pos
    output_pos: usize,
}

impl CopyNode {
    pub(crate) fn new(
        tag: String,
        parent_node: NodeIndex<u32>,
        node_index: NodeIndex<u32>,
        output_pos: usize,
    ) -> Self {
        Self {
            tag,
            parent_node,
            node_index,
            output_pos,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct OpNode {
    tag: String,
    // Store NodeIndex for debugging purposes
    node_index: NodeIndex<u32>,
    // Debugging purpoess
    high_node: NodeIndex<u32>,
    // Debugging purposes
    low_node: NodeIndex<u32>,
    output_pos: usize,
    high_index: usize,
    low_index: usize,
    input_index: usize,
}

impl OpNode {
    pub(crate) fn new(
        tag: String,
        node_index: NodeIndex<u32>,
        high_node: NodeIndex<u32>,
        low_node: NodeIndex<u32>,
        output_pos: usize,
        high_index: usize,
        low_index: usize,
        input_index: usize,
    ) -> Self {
        Self {
            tag,
            node_index,
            high_node,
            low_node,
            high_index,
            output_pos,
            low_index,
            input_index: input_index,
        }
    }

    pub(crate) fn input_index(&self) -> usize {
        self.input_index
    }

    pub(crate) fn low_index(&self) -> usize {
        self.low_index
    }

    pub(crate) fn high_index(&self) -> usize {
        self.high_index
    }
}

impl Display for OpNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "OpNode{{ tag: {}, node_index: {:?}, high_node: {:?}, low_node: {:?}, output_pos: {}, high_index: {}, low_index: {}, input_index: {} }}",
            self.tag,
            self.node_index,
            self.high_node,
            self.low_node,
            self.output_pos,
            self.high_index,
            self.low_index,
            self.input_index
        )
    }
}

impl Display for CopyNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CopyNode{{ tag: {}, parent_node: {:?}, node_index: {:?}, output_pos: {} }}",
            self.tag, self.parent_node, self.node_index, self.output_pos
        )
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Copy(copy_node) => write!(f, "{}", copy_node),
            Node::OpNode(op_node) => write!(f, "{}", op_node),
            Node::None => write!(f, "None"),
        }
    }
}

#[derive(Clone)]
pub(crate) struct UpdownBDD {
    level_nodes: Vec<Vec<Node>>,
}

impl UpdownBDD {
    fn new(level_nodes: Vec<Vec<Node>>) -> UpdownBDD {
        UpdownBDD { level_nodes }
    }

    pub(crate) fn level_nodes(&self) -> &[Vec<Node>] {
        &self.level_nodes
    }

    /// Width of the state vector
    pub(crate) fn width(&self) -> usize {
        // all levels have the same width
        //
        // minimum width is 2 to at-least account for terminal nodes
        std::cmp::max(2, self.level_nodes()[0].len())
    }

    #[allow(dead_code)]
    pub(crate) fn stats(&self) -> String {
        let depth = self.level_nodes.len();
        let mut output = String::new();

        output.push_str("UpdownBDD Statistics:\n");
        output.push_str("===================\n");
        output.push_str(&format!("Depth: {}\n", depth));
        output.push_str("\n");

        for (level_num, level) in self.level_nodes.iter().enumerate() {
            let mut copy_count = 0;
            let mut op_count = 0;
            let mut none_count = 0;

            for node in level {
                match node {
                    Node::Copy(_) => copy_count += 1,
                    Node::OpNode(_) => op_count += 1,
                    Node::None => none_count += 1,
                }
            }

            let total = copy_count + op_count + none_count;

            output.push_str(&format!(
                "Level {}: CopyNode: {}, OpNode: {}, None: {}, Total: {}\n",
                level_num, copy_count, op_count, none_count, total
            ));
        }

        output.push_str(&format!("Width: {}\n", self.width()));

        output
    }

    pub(crate) fn to_codegen(&self) -> CodegenUpDownBDD {
        // Flatten 2d vector level_nodes into 1d vector
        let mut nodes = Vec::new();
        let mut lvl_bounds = Vec::new();

        for level in self.level_nodes() {
            // Record the starting index of this level
            lvl_bounds.push(nodes.len());
            nodes.extend_from_slice(level.as_slice());
        }

        let max_inter_state = self.width();

        CodegenUpDownBDD::new(nodes, lvl_bounds, max_inter_state)
    }
}

impl Display for UpdownBDD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "UpdownBDD {{")?;
        for (level_num, level) in self.level_nodes.iter().enumerate() {
            write!(f, "    Level {}: ", level_num)?;
            for (i, node) in level.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", node)?;
            }
            writeln!(f)?;
        }
        writeln!(f, "}}")
    }
}

fn levels_for_graph(graph: &Graph<String, i32>) -> HashMap<NodeIndex, usize> {
    let top_sort = toposort(graph, Default::default()).unwrap();

    let mut level_map = HashMap::new();

    for i in 0..top_sort.len() {
        let mut level = 0;
        for incoming_edge in
            graph.edges_directed(top_sort[i], petgraph::Direction::Incoming)
        {
            let pred = incoming_edge.source();
            level = std::cmp::max(level, *level_map.get(&pred).unwrap() + 1);
        }
        assert!(level_map.insert(top_sort[i], level).is_none())
    }

    level_map
}

fn levelise_graph(
    graph: &mut Graph<String, i32>,
    levels: HashMap<NodeIndex, usize>,
) {
    let max_level = *levels.values().max().unwrap();
    for lvl in 0..max_level + 1 {
        for (node, _) in levels.iter().filter(|(_, l)| **l == lvl) {
            let node_weight = graph.node_weight(*node).unwrap().clone();

            let mut max_lvl_to_reach = lvl;
            let mut add_edges = vec![];
            let mut delete_edges = vec![];
            for out in graph.edges_directed(*node, Outgoing) {
                let node2 = out.target();
                let lvl_child = *levels.get(&node2).unwrap();
                max_lvl_to_reach = std::cmp::max(max_lvl_to_reach, lvl_child);
                add_edges.push((node2, lvl_child, *out.weight()));
                delete_edges.push(out.id());
            }

            // println!("{}: {}, {}", node_weight, lvl, max_lvl_to_reach);

            // delete old edges
            for e in delete_edges {
                graph.remove_edge(e);
            }

            // add dummy nodes
            // start node is at level = lvl
            let mut start = *node;
            for l in lvl + 1..max_lvl_to_reach + 1 {
                add_edges.iter().filter(|(_, cl, _)| *cl == l).for_each(
                    |(n, _, we)| {
                        graph.add_edge(start, *n, *we);
                    },
                );

                if l < max_lvl_to_reach {
                    let next = graph.add_node(node_weight.clone());
                    graph.add_edge(start, next, 2); // edge weight 2 implies copy
                    start = next;
                }
            }
        }
    }
}

fn translate_node_tag_to_input_index(
    node_tag: &String,
    input_order: &[String],
    alias_map: Option<&HashMap<String, String>>,
) -> usize {
    let dealiased_tag = alias_map
        .as_ref()
        .and_then(|m| m.get(node_tag).cloned())
        .unwrap_or(node_tag.clone());
    let input_index = input_order
        .iter()
        .position(|t| &dealiased_tag == t)
        .unwrap();

    input_index
}

// input_order: desired order of input variables at evaluation time
pub(crate) fn updown_bdd_from_bdd(
    bdd: &Bdd,
    vars: &BddVariableSet,
    input_order: &[String],
    alias_map: Option<&HashMap<String, String>>,
) -> UpdownBDD {
    let var_names = vars.variable_names();
    if var_names.len() != (bdd.num_vars() as usize) {
        panic!(
            "Bdd is incompatible with the variable set ({} vs. {} variables)",
            bdd.num_vars(),
            var_names.len()
        );
    }

    // Invert the BDD
    let mut graph = DiGraph::new();
    // Bdd pointer index -> NodeIndex
    let mut bdd_index_to_node_index = HashMap::new();
    let terminal_node0 = graph.add_node("0".to_string());
    let terminal_node1 = graph.add_node("1".to_string());
    bdd_index_to_node_index.insert(0, terminal_node0);
    bdd_index_to_node_index.insert(1, terminal_node1);
    // bdd.pointers().take(2).for_each(f);
    for node_pointer in bdd.pointers().skip(2) {
        // bdd's index must not repeat
        assert!(
            bdd_index_to_node_index
                .insert(
                    node_pointer.to_index(),
                    graph.add_node(
                        var_names[bdd.var_of(node_pointer).to_index()]
                            .to_string()
                    ),
                )
                .is_none()
        );
    }
    for node_pointer in bdd.pointers().skip(2) {
        let curr_node = bdd_index_to_node_index
            .get(&node_pointer.to_index())
            .unwrap();

        let high_link = bdd.high_link_of(node_pointer);
        let high_node =
            bdd_index_to_node_index.get(&high_link.to_index()).unwrap();
        // directed edge from high link node to curr node
        graph.add_edge(*high_node, *curr_node, 1);

        let low_link = bdd.low_link_of(node_pointer);
        let low_node =
            bdd_index_to_node_index.get(&low_link.to_index()).unwrap();
        // directed edge from low link node to curr node
        graph.add_edge(*low_node, *curr_node, 0);
    }

    // levelise the inverset BDD graph s.t. edge only exists between nodes that in consecutive
    // levels. We call the resulting graph: levelised graph
    {
        let levels = levels_for_graph(&graph);
        levelise_graph(&mut graph, levels);
        // println!("levelised udbdd {}", Dot::with_config(&graph, &[]));
    }

    // ==== process the levelised graph as a state vector machine ====

    let levels = levels_for_graph(&graph);
    let max_level = *levels.values().max().unwrap();
    let mut levels_to_nodes_map = HashMap::new();
    let mut max_width = 2;
    for l in 0..max_level + 1 {
        let set: HashSet<NodeIndex> = levels
            .iter()
            .filter(|(_, nl)| **nl == l)
            .map(|(n, _)| *n)
            .collect();
        max_width = std::cmp::max(max_width, set.len());
        levels_to_nodes_map.insert(l, set);
    }

    // {
    //     println!("Levels maps: ");
    //     for l in 0..max_level + 1 {
    //         println!("  {l}: {:?}", levels_to_nodes_map.get(&l).unwrap());
    //     }
    // }

    assert_eq!(
        levels_to_nodes_map.get(&0).unwrap(),
        &HashSet::from_iter([NodeIndex::new(0), NodeIndex::new(1)].into_iter())
    );
    let mut nodes_to_outpos = HashMap::new();
    nodes_to_outpos.insert(NodeIndex::new(0), 0usize);
    nodes_to_outpos.insert(NodeIndex::new(1), 1usize);

    let mut level_nodes = vec![];
    // skip the first and the last level
    for l in 1..max_level {
        let nodes_at_lvl = levels_to_nodes_map.get(&l).unwrap();
        let mut pos_set: HashSet<usize> = HashSet::from_iter(0usize..max_width);

        // Nodes are placed sorted by output position
        let mut curr_level = vec![Node::None; max_width];

        // handle copy nodes
        nodes_at_lvl.iter().filter_map(|n| {
            let incoming_edges =
                graph.edges_directed(*n, Incoming).collect_vec();
            assert!(incoming_edges.len() <= 2);
            if incoming_edges.len() == 1 {
                assert!(
                    incoming_edges[0].weight() == &2,
                    "Node has one incoming edge but with weight not equal to 2"
                );
                return Some((incoming_edges[0].source(), *n));
            }
            None
        }).for_each(|(parent_node, copy_node)| {
                let parent_pos = *nodes_to_outpos.get(&parent_node).unwrap();
                // println!("Copy node:{:?}, Parent node:{:?}, Parent Pos:{}, Parent lvl:{}", copy_node, parent_node, parent_pos, levels.get(&parent_node).unwrap());
                assert!(pos_set.remove(&parent_pos)==true, "Copy node pos is inuse but some other copy node");

                let node_weight = graph.node_weight(copy_node).unwrap().clone();
                curr_level[parent_pos]=Node::Copy(CopyNode::new(node_weight, parent_node, copy_node, parent_pos ));

                nodes_to_outpos.insert(copy_node, parent_pos);
            });

        // handle rest of the nodes
        nodes_at_lvl
            .iter()
            .filter_map(|n| {
                let mut incoming_edges =
                    graph.edges_directed(*n, Incoming).collect_vec();
                if incoming_edges.len() == 2 {
                    // sort edges: low_index, high_index
                    incoming_edges.sort_by(|a, b| a.weight().cmp(b.weight()));
                    assert!(
                        incoming_edges[0].weight() == &0
                            && incoming_edges[1].weight() == &1
                    );
                    // (low_node, high_node, curr_node)
                    return Some((
                        incoming_edges[0].source(),
                        incoming_edges[1].source(),
                        *n,
                    ));
                }
                None
            })
            .for_each(|(low_node, high_node, curr_node)| {
                let curr_pos = pos_set.iter().next().cloned().expect("Positions ran out before each node at level has a position");
                assert!(pos_set.remove(&curr_pos));

                let high_index =*nodes_to_outpos.get(&high_node).unwrap();
                let low_index =* nodes_to_outpos.get(&low_node).unwrap();
                let node_weight = graph.node_weight(curr_node).unwrap().clone();
                let input_index = translate_node_tag_to_input_index(&node_weight, input_order, alias_map);
                curr_level[curr_pos] = Node::OpNode(OpNode::new(node_weight, curr_node,high_node ,low_node, curr_pos, high_index, low_index, input_index));

                nodes_to_outpos.insert(curr_node, curr_pos);
            });

        // println!("Lvl {}: {:?}", l, curr_level);
        level_nodes.push(curr_level);
    }

    // process last level
    //
    // force output node output pos as 0
    {
        let output_node = levels_to_nodes_map.get(&max_level).unwrap();
        assert_eq!(output_node.len(), 1);
        let output_node = output_node.iter().last().unwrap().clone();

        let mut incoming_edges =
            graph.edges_directed(output_node, Incoming).collect_vec();
        incoming_edges.sort_by(|a, b| a.weight().cmp(b.weight()));
        assert!(
            incoming_edges[0].weight() == &0
                && incoming_edges[1].weight() == &1
        );
        let high_node = incoming_edges[1].source();
        let low_node = incoming_edges[0].source();

        let high_index = *nodes_to_outpos.get(&high_node).unwrap();
        let low_index = *nodes_to_outpos.get(&low_node).unwrap();
        let node_weight = graph.node_weight(output_node).unwrap().clone();
        let input_index = translate_node_tag_to_input_index(
            &node_weight,
            input_order,
            alias_map,
        );
        let mut tmp_vec = vec![Node::None; max_width];
        tmp_vec[0] = Node::OpNode(OpNode::new(
            node_weight,
            output_node,
            high_node,
            low_node,
            0,
            high_index,
            low_index,
            input_index,
        ));
        level_nodes.push(tmp_vec);

        nodes_to_outpos.insert(output_node, 0);
    }
    UpdownBDD::new(level_nodes)
}
