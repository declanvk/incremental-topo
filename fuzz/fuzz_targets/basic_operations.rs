#![no_main]

use arbitrary::Arbitrary;
use incremental_topo::{Error, IncrementalTopo, Node};
use libfuzzer_sys::fuzz_target;
use std::{cmp::Ordering, collections::HashSet};

#[derive(Debug, Arbitrary)]
pub enum IncrementalTopoMethod {
    AddNode,
    DeleteNode {
        node_index: usize,
    },
    AddDependency {
        prec_node_index: usize,
        succ_node_index: usize,
    },
    CheckContainsNode {
        node_index: usize,
    },
    ContainsDependency {
        prec_node_index: usize,
        succ_node_index: usize,
    },
    ContainsTransitiveDependency {
        prec_node_index: usize,
        succ_node_index: usize,
    },
    DeleteDependency {
        prec_node_index: usize,
        succ_node_index: usize,
    },
    CheckIsEmpty,
    CheckLen,
    IterateUnsorted,
    IterateDescendantsUnsorted {
        node_index: usize,
    },
    IterateDescendants {
        node_index: usize,
    },
    TopoCompare {
        node_a_index: usize,
        node_b_index: usize,
    },
}

#[derive(Debug, Default)]
struct FuzzState {
    nodes: Vec<Node>,
    graph: IncrementalTopo,
}

macro_rules! check_node_indices {
    ($nodes:expr, $($node_idx:expr),+) => {
        $(
            if $node_idx >= $nodes.len() {
                return Ok(());
            }
        )*
    }
}

impl FuzzState {
    fn apply_method(&mut self, method: IncrementalTopoMethod) -> Result<(), Error> {
        use IncrementalTopoMethod::*;

        match method {
            TopoCompare {
                node_a_index,
                node_b_index,
            } => {
                check_node_indices!(self.nodes, node_a_index, node_b_index);

                let node_a = self.nodes[node_a_index];
                let node_b = self.nodes[node_b_index];

                let cmp = self.graph.topo_cmp(node_a, node_b);

                if node_a == node_b {
                    assert_eq!(cmp, Ordering::Equal);
                } else {
                    assert!(cmp == Ordering::Greater || cmp == Ordering::Less);
                }
            },
            IterateDescendants { node_index } => {
                check_node_indices!(self.nodes, node_index);

                let parent_node = self.nodes[node_index];

                let descendants = self.graph.descendants(parent_node);

                descendants?.for_each(|descendant_node| {
                    assert_eq!(
                        self.graph.topo_cmp(parent_node, descendant_node),
                        Ordering::Less
                    );
                });
            },
            IterateDescendantsUnsorted { node_index } => {
                check_node_indices!(self.nodes, node_index);

                let parent_node = self.nodes[node_index];

                let descendants = self.graph.descendants_unsorted(parent_node);

                descendants?.for_each(|(_, descendant_node)| {
                    assert_eq!(
                        self.graph.topo_cmp(parent_node, descendant_node),
                        Ordering::Less,
                        "Expected descendant [{:?}] to be greater in topo order than ancestor \
                         [{:?}]. Graph [{:?}]",
                        descendant_node,
                        parent_node,
                        self.graph
                    );
                });
            },
            IterateUnsorted => {
                let nodes_from_iter = self
                    .graph
                    .iter_unsorted()
                    .map(|(_, node)| node)
                    .collect::<HashSet<_>>();

                for node in &self.nodes {
                    assert!(
                        nodes_from_iter.contains(node),
                        "Expected node [{:?}] to be present in fuzz state and graph",
                        node
                    );
                }
            },
            CheckIsEmpty => {
                assert_eq!(self.nodes.is_empty(), self.graph.is_empty());
            },
            CheckLen => {
                assert_eq!(self.nodes.len(), self.graph.len());
            },
            DeleteDependency {
                succ_node_index,
                prec_node_index,
            } => {
                check_node_indices!(self.nodes, succ_node_index, prec_node_index);
                let prec = self.nodes[prec_node_index];
                let succ = self.nodes[succ_node_index];

                let _ = self.graph.delete_dependency(prec, succ);
            },
            ContainsTransitiveDependency {
                succ_node_index,
                prec_node_index,
            } => {
                check_node_indices!(self.nodes, succ_node_index, prec_node_index);
                let prec = self.nodes[prec_node_index];
                let succ = self.nodes[succ_node_index];

                let _ = self.graph.contains_transitive_dependency(prec, succ);
            },
            ContainsDependency {
                succ_node_index,
                prec_node_index,
            } => {
                check_node_indices!(self.nodes, succ_node_index, prec_node_index);
                let prec = self.nodes[prec_node_index];
                let succ = self.nodes[succ_node_index];

                let _ = self.graph.contains_dependency(prec, succ);
            },
            AddDependency {
                succ_node_index,
                prec_node_index,
            } => {
                check_node_indices!(self.nodes, succ_node_index, prec_node_index);
                let prec = self.nodes[prec_node_index];
                let succ = self.nodes[succ_node_index];

                let _ = self.graph.add_dependency(prec, succ)?;
            },
            DeleteNode { node_index } => {
                check_node_indices!(self.nodes, node_index);
                let node = self.nodes[node_index];

                assert!(self.graph.delete_node(node));

                self.nodes.remove(node_index);
            },
            CheckContainsNode { node_index } => {
                check_node_indices!(self.nodes, node_index);
                let node = self.nodes[node_index];

                assert!(self.graph.contains_node(node));
            },
            AddNode => {
                let new_node = self.graph.add_node();
                self.nodes.push(new_node);
            },
        }

        Ok(())
    }
}

fuzz_target!(|methods: Vec<IncrementalTopoMethod>| {
    let mut fuzz_state = FuzzState::default();

    for method in methods {
        let _ = fuzz_state.apply_method(method);
    }
});
