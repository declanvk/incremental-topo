//! This regression was discovered by fuzzing on the main operations of the
//! `IncrementalTopo`. The fuzz input was:
//!
//! ```rust
//! [
//!     AddNode,
//!     TopoCompare {
//!         node_a_index: 65791,
//!         node_b_index: 4982833243,
//!     },
//!     AddNode,
//!     AddNode,
//!     AddNode,
//!     AddNode,
//!     ContainsDependency {
//!         prec_node_index: 54645770850140249,
//!         succ_node_index: 0,
//!     },
//!     AddNode,
//!     AddDependency {
//!         prec_node_index: 1,
//!         succ_node_index: 0,
//!     },
//!     AddNode,
//!     TopoCompare {
//!         node_a_index: 3096224743817215,
//!         node_b_index: 213305255788544,
//!     },
//!     AddNode,
//!     AddNode,
//!     AddDependency {
//!         prec_node_index: 0,
//!         succ_node_index: 1,
//!     },
//!     AddNode,
//!     AddNode,
//!     AddNode,
//!     AddNode,
//!     AddNode,
//!     IterateDescendantsUnsorted {
//!         node_index: 0,
//!     },
//! ]
//! ```
//!
//! Remove invalid operations and redundant node creations, the input should
//! reduce to:
//!
//! ```rust
//! [
//!     AddNode,
//!     AddNode,
//!     AddDependency {
//!         prec_node_index: 1,
//!         succ_node_index: 0,
//!     },
//!     AddDependency {
//!         prec_node_index: 0,
//!         succ_node_index: 1,
//!     },
//!     IterateDescendantsUnsorted {
//!         node_index: 0,
//!     },
//! ]
//! ```
//!
//! It turns out that the issue was that the `add_dependency` was incorrectly
//! updating the `parents` & `children` sets for the nodes, but not undoing this
//! update when it turns out that the issue introduced an
//! [`incremental_topo::Error::CycleDetected`].
//!
//! Looking at debug format of the graph before and after calling the
//! `add_dependency` which returns the cycle error shows the incorrectly updated
//! information.
//!
//! Before:
//! ```
//! IncrementalTopo {
//!     node_data: [
//!         NodeData { topo_order: 2, parents: {UnsafeIndex(1)}, children: {              } },
//!         NodeData { topo_order: 1, parents: {              }, children: {UnsafeIndex(0)} }
//!     ]
//! }
//! ```
//!
//! After
//! ```
//! IncrementalTopo {
//!     node_data: [
//!         NodeData { topo_order: 2, parents: {UnsafeIndex(1)}, children: {UnsafeIndex(1)} },
//!         NodeData { topo_order: 1, parents: {UnsafeIndex(0)}, children: {UnsafeIndex(0)} }
//!     ]
//! }
//! ```

use std::cmp::Ordering;

#[test]
fn descendants_unsorted_cycle_regression() {
    let mut graph = incremental_topo::IncrementalTopo::default();

    let n0 = graph.add_node();
    let n1 = graph.add_node();

    assert_eq!(graph.add_dependency(n1, n0), Ok(true));

    // Here we check that the descendants (all 1) have a topo ordering that is
    // greater than the ancestor which succeeds
    assert_eq!(
        1,
        graph
            .descendants_unsorted(n1)
            .unwrap()
            .inspect(|(_, descendant_node)| {
                assert_eq!(
                    graph.topo_cmp(n1, descendant_node),
                    Ordering::Less,
                    "Expected descendant [{:?}] to be greater in topo order than ancestor [{:?}]",
                    descendant_node,
                    n0
                );
            })
            .count()
    );

    assert_eq!(
        graph.add_dependency(n0, n1),
        Err(incremental_topo::Error::CycleDetected)
    );

    // We expect that the n0 node has no descendants because the previous
    // `add_dependency` call failed
    assert_eq!(
        0,
        graph
            .descendants_unsorted(n0)
            .unwrap()
            .inspect(|(_, descendant_node)| {
                assert_eq!(
                    graph.topo_cmp(n0, descendant_node),
                    Ordering::Less,
                    "Expected descendant [{:?}] to be greater in topo order than ancestor [{:?}]. \
                     Graph {:?}",
                    descendant_node,
                    n0,
                    graph
                );
            })
            .count()
    );

    // Here we check again that the descendants (all 1) have a topo ordering that is
    // greater than the ancestor which succeeds
    assert_eq!(
        1,
        graph
            .descendants_unsorted(n1)
            .unwrap()
            .inspect(|(_, descendant_node)| {
                assert_eq!(
                    graph.topo_cmp(n1, descendant_node),
                    Ordering::Less,
                    "Expected descendant [{:?}] to be greater in topo order than ancestor [{:?}]",
                    descendant_node,
                    n0
                );
            })
            .count()
    );
}
