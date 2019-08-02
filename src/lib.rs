//! The purpose of this crate is to maintain an topological order in the face
//! of single updates, like adding new nodes, adding new depedencies, deleting
//! dependencies, and deleting nodes.
//!
//! Adding nodes, deleting nodes, and deleting dependencies require a trivial
//! amount of work to perform an update, because those operations do not change
//! the topological ordering. Adding new dependencies does
//!
//! ## What is a Topological Order
//!
//! To define a topological order requires at least simple definitions of a
//! graph, and specifically a directed acyclic graph (DAG). A graph can be
//! described as a pair of sets, `(V, E)` where `V` is the set of all nodes in
//! the graph, and `E` is the set of edges. An edge is defined as a pair, `(m,
//! n)` where `m` and `n` are nodes. A directed graph means that edges only
//! imply a single direction of relationship between two nodes, as opposed to a
//! undirected graph which implies the relationship goes both ways. An example
//! of undirected vs. directed in social networks would be Facebook vs.
//! Twitter. Facebook friendship is a two way relationship, while following
//! someone on Twitter does not imply that they follow you back.
//!
//! A topological ordering, `ord_D` of a directed acyclic graph, `D = (V, E)`
//! where `x, y ∈ V`, is a mapping of nodes to priority values such that
//! `ord_D(x) < ord_D(y)` holds for all edges `(x, y) ∈ E`. This yields a total
//! ordering of the nodes in `D`.
//!
//! ## Examples
//!
//! ```
//! use incremental_topo::IncrementalTopo;
//! use std::{cmp::Ordering::*, collections::HashSet};
//!
//! let mut dag = IncrementalTopo::new();
//!
//! dag.add_node("dog");
//! dag.add_node("cat");
//! dag.add_node("mouse");
//! dag.add_node("lion");
//! dag.add_node("human");
//! dag.add_node("gazelle");
//! dag.add_node("grass");
//!
//! assert_eq!(dag.size(), 7);
//!
//! dag.add_dependency("lion", "human").unwrap();
//! dag.add_dependency("lion", "gazelle").unwrap();
//!
//! dag.add_dependency("human", "dog").unwrap();
//! dag.add_dependency("human", "cat").unwrap();
//!
//! dag.add_dependency("dog", "cat").unwrap();
//! dag.add_dependency("cat", "mouse").unwrap();
//!
//! dag.add_dependency("gazelle", "grass").unwrap();
//!
//! dag.add_dependency("mouse", "grass").unwrap();
//!
//! let pairs = dag
//!     .descendants_unsorted("human")
//!     .unwrap()
//!     .collect::<HashSet<_>>();
//! let expected_pairs = [(4, &"cat"), (3, &"dog"), (5, &"mouse"), (7, &"grass")]
//!     .iter()
//!     .cloned()
//!     .collect::<HashSet<_>>();
//!
//! assert_eq!(pairs, expected_pairs);
//!
//! assert!(dag.contains_transitive_dependency("lion", "grass"));
//! assert!(!dag.contains_transitive_dependency("human", "gazelle"));
//!
//! assert_eq!(dag.topo_cmp("cat", "dog").unwrap(), Greater);
//! assert_eq!(dag.topo_cmp("lion", "human").unwrap(), Less);
//! ```
//!
//! ## Sources
//!
//! The [paper by D. J. Pearce and P. H. J. Kelly] contains descriptions of
//! three different algorithms for incremental topological ordering, along with
//! analysis of runtime bounds for each.
//!
//! [paper by D. J. Pearce and P. H. J. Kelly]: http://www.doc.ic.ac.uk/~phjk/Publications/DynamicTopoSortAlg-JEA-07.pdf

pub mod bimap;

use bimap::BiMap;
use core::{
    borrow::Borrow,
    cmp::{Ordering, Reverse},
    hash::Hash,
    iter::Iterator,
};
use failure_derive::Fail;
use slab::Slab;
use std::collections::{BinaryHeap, HashSet};

/// Data structure for maintaining a topological ordering over a collection of
/// elements, in an incremental fashion.
///
/// See the [module-level documentation] for more information.
///
/// [module-level documentation]: index.html
#[derive(Default, Debug, Clone)]
pub struct IncrementalTopo<T: Hash + Eq, NodeId: Hash + Eq + Copy = usize> {
    node_keys: BiMap<T, usize>,
    node_data: Slab<NodeData<NodeId>>,
    last_topo_order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NodeData<NodeId: Hash + Eq> {
    topo_order: u32,
    parents: HashSet<NodeId>,
    children: HashSet<NodeId>,
}

impl<NodeId> NodeData<NodeId>
where
    NodeId: Hash + Eq,
{
    fn new(topo_order: u32) -> Self {
        NodeData {
            topo_order,
            parents: HashSet::new(),
            children: HashSet::new(),
        }
    }
}

impl<NodeId: Hash + Eq> PartialOrd for NodeData<NodeId> {
    fn partial_cmp(&self, other: &NodeData<NodeId>) -> Option<Ordering> {
        self.topo_order.partial_cmp(&other.topo_order)
    }
}

impl<NodeId: Hash + Eq> Ord for NodeData<NodeId> {
    fn cmp(&self, other: &NodeData<NodeId>) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Different types of failures that can occur while updating or querying the
/// graph.
#[derive(Fail, Debug)]
pub enum Error {
    #[fail(display = "Node was not found in graph")]
    NodeMissing,
    #[fail(display = "Nodes may not transitively depend on themselves in a cyclic fashion")]
    CycleDetected,
}

pub type Result<T> = std::result::Result<T, Error>;

impl<T: Hash + Eq> IncrementalTopo<T> {
    /// Create a new IncrementalTopo graph.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let dag = IncrementalTopo::<usize>::new();
    ///
    /// assert!(dag.is_empty());
    /// ```
    pub fn new() -> Self {
        IncrementalTopo {
            node_keys: BiMap::new(),
            node_data: Slab::new(),
            last_topo_order: 0,
        }
    }

    /// Add a new node to the graph.
    ///
    /// Initially this node will not have any order relative to the values
    /// that are already in the graph. Only when relations are added
    /// with [`add_dependency`] will the order begin to matter.
    ///
    /// Returns false if the graph already contains the node.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("dog"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    ///
    /// assert!(!dag.add_node("cat"));
    /// ```
    ///
    /// [`add_dependency`]: struct.IncrementalTopo.html#method.add_dependency
    pub fn add_node(&mut self, node: T) -> bool {
        if self.contains_node(&node) {
            return false;
        }

        let next_topo_order = self.last_topo_order + 1;
        let node_entry = self.node_data.vacant_entry();
        let key = node_entry.key();
        let node_data = NodeData::new(next_topo_order);

        log::info!("Created {:?} at key {:?}", node_data, key);

        self.node_keys.insert(node, key);

        node_entry.insert(node_data);

        self.last_topo_order = next_topo_order;

        true
    }

    /// Returns true if the graph contains the specified node.
    ///
    /// The passed node may be any borrowed form of the graph's node type, but
    /// Hash and Eq on the borrowed form must match those for the node type.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert!(dag.contains_node("cat"));
    /// assert!(dag.contains_node("dog"));
    ///
    /// assert!(!dag.contains_node("horse"));
    /// assert!(!dag.contains_node("orc"));
    /// ```
    pub fn contains_node<Q>(&self, node: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.node_keys.contains_left(node)
    }

    /// Attempt to remove node from graph, returning true if the node was
    /// contained and removed.
    ///
    /// The passed node may be any borrowed form of the graph's node type, but
    /// Hash and Eq on the borrowed form must match those for the node type.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert!(dag.delete_node("cat"));
    /// assert!(dag.delete_node(&"dog"));
    ///
    /// assert!(!dag.delete_node("horse"));
    /// assert!(!dag.delete_node(&"orc"));
    /// ```
    pub fn delete_node<Q>(&mut self, node: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some((_, key)) = self.node_keys.remove_by_left(node) {
            // Remove associated data
            let data = self.node_data.remove(key);

            // Delete forward edges
            for child in data.children {
                if let Some(child_data) = self.node_data.get_mut(child) {
                    child_data.parents.remove(&key);
                }
            }

            // Delete backward edges
            for parent in data.parents {
                if let Some(parent_data) = self.node_data.get_mut(parent) {
                    parent_data.children.remove(&key);
                }
            }

            // TODO Fix inefficient compaction step
            for key in self.node_keys.right_values() {
                if let Some(node_data) = self.node_data.get_mut(*key) {
                    if node_data.topo_order > data.topo_order {
                        node_data.topo_order -= 1;
                    }
                }
            }

            // Decrement last topo order to account for shifted topo values
            self.last_topo_order -= 1;

            true
        } else {
            false
        }
    }

    /// Add a directed link between two nodes already present in the graph.
    ///
    /// This link indicates an ordering constraint on the two nodes, now `prec`
    /// must always come before `succ` in the ordering.
    ///
    /// The values of `prec` and `succ` may be any borrowed form of the graph's
    /// node type, but Hash and Eq on the borrowed form must match those for
    /// the node type.
    ///
    /// Returns `Ok(true)` if the graph did not previously contain this
    /// dependency. Returns `Ok(false)` if the graph did have a previous
    /// dependency between these two nodes.
    ///
    /// # Errors
    /// This function will return an `Err` if the dependency introduces a cycle
    /// into the graph or if either of the nodes passed is not found in the
    /// graph.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("dog"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    ///
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    /// ```
    pub fn add_dependency<Q, R>(&mut self, prec: &Q, succ: &R) -> Result<bool>
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        let (prec_key, succ_key) = self.get_dep_keys(prec, succ)?;

        if prec_key == succ_key {
            // No loops to self
            return Err(Error::CycleDetected);
        }

        // Insert forward edge
        let mut no_prev_edge = self.node_data[prec_key].children.insert(succ_key);
        let upper_bound = self.node_data[prec_key].topo_order;

        // Insert backward edge
        no_prev_edge = no_prev_edge && self.node_data[succ_key].parents.insert(prec_key);
        let lower_bound = self.node_data[succ_key].topo_order;

        // If edge already exists short circuit
        if !no_prev_edge {
            return Ok(false);
        }

        log::info!("Adding edge from {:?} to {:?}", prec_key, succ_key);

        log::trace!(
            "Upper: Order({}), Lower: Order({})",
            upper_bound,
            lower_bound
        );
        // If the affected region of the graph has non-zero size (i.e. the upper and
        // lower bound are equal) then perform an update to the topological ordering of
        // the graph
        if lower_bound < upper_bound {
            log::trace!("Will change");
            let mut visited = HashSet::new();

            // Walk changes forward from the succ, checking for any cycles that would be
            // introduced
            let change_forward = self.dfs_forward(succ_key, &mut visited, upper_bound)?;
            log::trace!("Change forward: {:?}", change_forward);
            // Walk backwards from the prec
            let change_backward = self.dfs_backward(prec_key, &mut visited, lower_bound);
            log::trace!("Change backward: {:?}", change_backward);

            self.reorder_nodes(change_forward, change_backward);

            log::trace!(
                "Final order: {:?}",
                self.node_keys
                    .right_values()
                    .map(|key| {
                        let order = self.node_data[*key].topo_order;
                        (order, key)
                    })
                    .collect::<Vec<_>>()
            );
        } else {
            log::trace!("No change");
        }

        Ok(true)
    }

    /// Returns true if the graph contains a dependency from `prec` to `succ`.
    ///
    /// Returns false if either node is not found, or if there is no dependency.
    ///
    /// The values of `prec` and `succ` may be any borrowed form of the graph's
    /// node type, but Hash and Eq on the borrowed form must match those for
    /// the node type.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// assert!(dag.contains_dependency("cat", "mouse"));
    /// assert!(!dag.contains_dependency("human", "mouse"));
    /// assert!(!dag.contains_dependency("cat", "horse"));
    /// ```
    pub fn contains_dependency<Q, R>(&self, prec: &Q, succ: &R) -> bool
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        let (prec_key, succ_key) = match self.get_dep_keys(prec, succ) {
            Ok(val) => val,
            _ => return false,
        };

        self.node_data[prec_key].children.contains(&succ_key)
    }

    /// Returns true if the graph contains a transitive dependency from `prec`
    /// to `succ`.
    ///
    /// In this context a transitive dependency means that `succ` exists as a
    /// descendant of `prec`, with some chain of other nodes in between.
    ///
    /// Returns false if either node is not found in the graph, or there is no
    /// transitive dependency.
    ///
    /// The values of `prec` and `succ` may be any borrowed form of the graph's
    /// node type, but Hash and Eq on the borrowed form must match those for
    /// the node type.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// assert!(dag.contains_transitive_dependency("human", "mouse"));
    /// assert!(!dag.contains_transitive_dependency("dog", "mouse"));
    /// ```
    pub fn contains_transitive_dependency<Q, R>(&self, prec: &Q, succ: &R) -> bool
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        // If either node is missing, return quick
        let (prec_key, succ_key) = match self.get_dep_keys(prec, succ) {
            Ok(val) => val,
            _ => return false,
        };

        // A node cannot depend on itself
        if prec_key == succ_key {
            return false;
        }

        // Else we have to search the graph. Using dfs in this case because it avoids
        // the overhead of the binary heap, and this task doesn't really need ordered
        // descendants.
        let mut stack = Vec::new();
        let mut visited = HashSet::new();

        stack.push(prec_key);

        // For each node key popped off the stack, check that we haven't seen it
        // before, then check if its children contain the node we're searching for.
        // If they don't, continue the search by extending the stack with the children.
        while let Some(key) = stack.pop() {
            if visited.contains(&key) {
                continue;
            } else {
                visited.insert(key);
            }

            let children = &self.node_data[key].children;

            if children.contains(&succ_key) {
                return true;
            } else {
                stack.extend(children);

                continue;
            }
        }

        // If we exhaust the stack, then there is no transitive dependency.
        false
    }

    /// Attempt to remove a dependency from the graph, returning true if the
    /// dependency was removed.
    ///
    /// Returns false is either node is not found in the graph.
    ///
    /// The values of `prec` and `succ` may be any borrowed form of the graph's
    /// node type, but Hash and Eq on the borrowed form must match those for
    /// the node type.
    ///
    /// Removing a dependency from the graph is an extremely simple operation,
    /// which requires no recalculation of the topological order. The ordering
    /// before and after a removal is exactly the same.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// assert!(dag.delete_dependency("cat", "mouse"));
    /// assert!(dag.delete_dependency("human", "dog"));
    /// assert!(!dag.delete_dependency("human", "mouse"));
    /// ```
    pub fn delete_dependency<Q, R>(&mut self, prec: &Q, succ: &R) -> bool
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        let (prec_key, succ_key) = match self.get_dep_keys(prec, succ) {
            Ok(val) => val,
            _ => return false,
        };

        let prec_children = &mut self.node_data[prec_key].children;

        if !prec_children.contains(&succ_key) {
            return false;
        }

        prec_children.remove(&succ_key);
        self.node_data[succ_key].parents.remove(&prec_key);

        true
    }

    /// Return the number of nodes within the graph.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert_eq!(dag.size(), 4);
    /// ```
    pub fn size(&self) -> usize {
        self.node_keys.len()
    }

    /// Return true if there are no nodes in the graph.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.is_empty());
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert!(!dag.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Return an iterator over the nodes of the graph
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// use std::collections::HashSet;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("human"));
    /// assert!(dag.add_node("dog"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// let pairs = dag.iter_unsorted().collect::<HashSet<_>>();
    ///
    /// let mut expected_pairs = HashSet::new();
    /// expected_pairs.extend(vec![(1, &"human"), (2, &"cat"), (3, &"mouse"), (4, &"dog")]);
    ///
    /// assert_eq!(pairs, expected_pairs);
    /// ```
    pub fn iter_unsorted(&self) -> impl Iterator<Item = (u32, &T)> {
        self.node_keys.iter().map(move |(node, key)| {
            let order = self.node_data[*key].topo_order;

            (order, node)
        })
    }

    // FIXME(#1) mutable access not to be allowed
    // pub fn iter_mut(&mut self) -> bimap::ValuesMut<T> {
    //     self.node_keys.left_values_mut()
    // }

    /// Return an iterator over the descendants of a node in the graph, in an
    /// unosrted order.
    ///
    /// The passed node may be any borrowed form of the graph's node type, but
    /// Hash and Eq on the borrowed form must match those for the node type.
    ///
    /// Accessing the nodes in an unsorted order allows for faster access using
    /// a iterative DFS search. This is opposed to the order descendants
    /// iterator which requires the use of a binary heap to order the values.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// use std::collections::HashSet;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("dog"));
    /// assert!(dag.add_node("human"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("dog", "cat").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// let pairs = dag
    ///     .descendants_unsorted("human")
    ///     .unwrap()
    ///     .collect::<HashSet<_>>();
    ///
    /// let mut expected_pairs = HashSet::new();
    /// expected_pairs.extend(vec![(2, &"dog"), (3, &"cat"), (4, &"mouse")]);
    ///
    /// assert_eq!(pairs, expected_pairs);
    /// ```
    pub fn descendants_unsorted<Q>(&self, node: &Q) -> Result<DescendantsUnsorted<T>>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let node_key = if let Some(key) = self.node_keys.get_by_left(node) {
            *key
        } else {
            return Err(Error::NodeMissing);
        };

        let mut stack = Vec::new();
        let visited = HashSet::new();

        // Add all children of selected node
        stack.extend(&self.node_data[node_key].children);

        Ok(DescendantsUnsorted {
            dag: self,
            stack,
            visited,
        })
    }

    /// Return an iterator over descendants of a node in the graph, in a
    /// topologically sorted order.
    ///
    /// The passed node may be any borrowed form of the graph's node type, but
    /// Hash and Eq on the borrowed form must match those for the node type.
    ///
    /// Accessing the nodes in a sorted order requires the use of a BinaryHeap,
    /// so some performance penalty is paid there. If all is required is access
    /// to the descendants of a node, use [`descendants_unsorted`].
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("dog"));
    /// assert!(dag.add_node("human"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("dog", "cat").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// let ordered_nodes = dag.descendants("human").unwrap().collect::<Vec<_>>();
    ///
    /// assert_eq!(ordered_nodes, vec![&"dog", &"cat", &"mouse"]);
    /// ```
    ///
    /// [`descendants_unsorted`]:
    /// struct.IncrementalTopo.html#method.descendants_unsorted
    pub fn descendants<Q>(&self, node: &Q) -> Result<Descendants<T>>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let node_key = if let Some(key) = self.node_keys.get_by_left(node) {
            *key
        } else {
            return Err(Error::NodeMissing);
        };

        let mut queue = BinaryHeap::new();

        // Add all children of selected node
        queue.extend(
            self.node_data[node_key]
                .children
                .iter()
                .cloned()
                .map(|child_key| {
                    let child_order = self.node_data[child_key].topo_order;
                    (Reverse(child_order), child_key)
                }),
        );

        let visited = HashSet::new();

        Ok(Descendants {
            dag: self,
            queue,
            visited,
        })
    }

    /// Compare two nodes present in the graph, topographically. Returns
    /// Err(...) if either node is missing from the graph.
    ///
    /// The values of `prec` and `succ` may be any borrowed form of the graph's
    /// node type, but Hash and Eq on the borrowed form must match those for
    /// the node type.
    ///
    /// # Examples
    /// ```
    /// use incremental_topo::IncrementalTopo;
    /// use std::cmp::Ordering::*;
    /// let mut dag = IncrementalTopo::new();
    ///
    /// assert!(dag.add_node("cat"));
    /// assert!(dag.add_node("mouse"));
    /// assert!(dag.add_node("dog"));
    /// assert!(dag.add_node("human"));
    ///
    /// assert!(dag.add_dependency("human", "cat").unwrap());
    /// assert!(dag.add_dependency("human", "dog").unwrap());
    /// assert!(dag.add_dependency("dog", "cat").unwrap());
    /// assert!(dag.add_dependency("cat", "mouse").unwrap());
    ///
    /// assert_eq!(dag.topo_cmp("human", "mouse").unwrap(), Less);
    /// assert_eq!(dag.topo_cmp("cat", "dog").unwrap(), Greater);
    /// assert!(dag.topo_cmp("cat", "horse").is_err());
    /// ```
    pub fn topo_cmp<Q, R>(&self, node_a: &Q, node_b: &R) -> Result<Ordering>
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        let (key_a, key_b) = self.get_dep_keys(node_a, node_b)?;

        Ok(self.node_data[key_a]
            .topo_order
            .cmp(&self.node_data[key_b].topo_order))
    }

    fn get_dep_keys<Q, R>(&self, prec: &Q, succ: &R) -> Result<(usize, usize)>
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        match (
            self.node_keys.get_by_left(prec),
            self.node_keys.get_by_left(succ),
        ) {
            (Some(p), Some(s)) => Ok((*p, *s)),
            _ => Err(Error::NodeMissing),
        }
    }

    fn dfs_forward(
        &self,
        start_key: usize,
        visited: &mut HashSet<usize>,
        upper_bound: u32,
    ) -> Result<HashSet<usize>> {
        let mut stack = Vec::new();
        let mut result = HashSet::new();

        stack.push(start_key);

        while let Some(next_key) = stack.pop() {
            visited.insert(next_key);
            result.insert(next_key);

            for child_key in &self.node_data[next_key].children {
                let child_topo_order = self.node_data[*child_key].topo_order;

                if child_topo_order == upper_bound {
                    return Err(Error::CycleDetected);
                }

                if !visited.contains(&child_key) && child_topo_order < upper_bound {
                    stack.push(*child_key);
                }
            }
        }

        Ok(result)
    }

    fn dfs_backward(
        &self,
        start_key: usize,
        visited: &mut HashSet<usize>,
        lower_bound: u32,
    ) -> HashSet<usize> {
        let mut stack = Vec::new();
        let mut result = HashSet::new();

        stack.push(start_key);

        while let Some(next_key) = stack.pop() {
            visited.insert(next_key);
            result.insert(next_key);

            for parent_key in &self.node_data[next_key].parents {
                let parent_topo_order = self.node_data[*parent_key].topo_order;

                if !visited.contains(&parent_key) && lower_bound < parent_topo_order {
                    stack.push(*parent_key);
                }
            }
        }

        result
    }

    fn reorder_nodes(&mut self, change_forward: HashSet<usize>, change_backward: HashSet<usize>) {
        let mut change_forward: Vec<_> = change_forward
            .into_iter()
            .map(|key| (key, self.node_data[key].topo_order))
            .collect();
        change_forward.sort_unstable_by_key(|pair| pair.1);

        let mut change_backward: Vec<_> = change_backward
            .into_iter()
            .map(|key| (key, self.node_data[key].topo_order))
            .collect();
        change_backward.sort_unstable_by_key(|pair| pair.1);

        let mut all_keys = Vec::new();
        let mut all_topo_orders = Vec::new();

        for (key, topo_order) in change_backward {
            all_keys.push(key);
            all_topo_orders.push(topo_order);
        }

        for (key, topo_order) in change_forward {
            all_keys.push(key);
            all_topo_orders.push(topo_order);
        }

        all_topo_orders.sort_unstable();

        for (key, topo_order) in all_keys.into_iter().zip(all_topo_orders.into_iter()) {
            self.node_data[key].topo_order = topo_order;
        }
    }
}

pub struct DescendantsUnsorted<'a, T>
where
    T: 'a + Eq + Hash,
{
    dag: &'a IncrementalTopo<T>,
    stack: Vec<usize>,
    visited: HashSet<usize>,
}

impl<'a, T> Iterator for DescendantsUnsorted<'a, T>
where
    T: 'a + Hash + Eq,
{
    type Item = (u32, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(key) = self.stack.pop() {
            if self.visited.contains(&key) {
                continue;
            } else {
                self.visited.insert(key);
            }

            let node = self.dag.node_keys.get_by_right(&key).unwrap();
            let order = self.dag.node_data[key].topo_order;

            self.stack.extend(&self.dag.node_data[key].children);

            return Some((order, node));
        }

        None
    }
}

pub struct Descendants<'a, T>
where
    T: 'a + Eq + Hash,
{
    dag: &'a IncrementalTopo<T>,
    queue: BinaryHeap<(Reverse<u32>, usize)>,
    visited: HashSet<usize>,
}

impl<'a, T> Iterator for Descendants<'a, T>
where
    T: 'a + Hash + Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((_, key)) = self.queue.pop() {
                if self.visited.contains(&key) {
                    continue;
                } else {
                    self.visited.insert(key);
                }

                let node = self.dag.node_keys.get_by_right(&key).unwrap();

                for child in &self.dag.node_data[key].children {
                    let order = self.dag.node_data[*child].topo_order;
                    self.queue.push((Reverse(order), *child))
                }

                return Some(node);
            } else {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate pretty_env_logger;
    use super::*;

    fn get_basic_dag() -> Result<IncrementalTopo<&'static str>> {
        let mut dag = IncrementalTopo::new();

        dag.add_node("dog");
        dag.add_node("cat");
        dag.add_node("mouse");
        dag.add_node("lion");
        dag.add_node("human");
        dag.add_node("gazelle");
        dag.add_node("grass");

        assert_eq!(dag.size(), 7);

        dag.add_dependency("lion", "human")?;
        dag.add_dependency("lion", "gazelle")?;

        dag.add_dependency("human", "dog")?;
        dag.add_dependency("human", "cat")?;

        dag.add_dependency("dog", "cat")?;
        dag.add_dependency("cat", "mouse")?;

        dag.add_dependency("gazelle", "grass")?;

        dag.add_dependency("mouse", "grass")?;

        Ok(dag)
    }

    #[test]
    fn add_nodes_basic() {
        let mut dag = IncrementalTopo::new();

        dag.add_node("dog");
        dag.add_node("cat");
        dag.add_node("mouse");
        dag.add_node("lion");
        dag.add_node("human");

        assert_eq!(dag.size(), 5);
        assert!(dag.contains_node("dog"));
        assert!(dag.contains_node("cat"));
        assert!(dag.contains_node("mouse"));
        assert!(dag.contains_node("lion"));
        assert!(dag.contains_node("human"));
    }

    #[test]
    fn add_nodes_duplicate() {
        let mut dag = IncrementalTopo::new();

        dag.add_node("dog");
        assert!(!dag.add_node("dog"));
        dag.add_node("cat");
        assert!(!dag.add_node("cat"));
        dag.add_node("human");

        assert_eq!(dag.size(), 3);

        assert!(dag.contains_node("dog"));
        assert!(dag.contains_node("cat"));
        assert!(dag.contains_node("human"));
    }

    #[test]
    fn delete_nodes() {
        let mut dag = IncrementalTopo::new();

        dag.add_node("dog");
        dag.add_node("cat");
        dag.add_node("human");

        assert_eq!(dag.size(), 3);

        assert!(dag.contains_node("dog"));
        assert!(dag.contains_node("cat"));
        assert!(dag.contains_node("human"));

        assert!(dag.delete_node("human"));
        assert_eq!(dag.size(), 2);
        assert!(!dag.contains_node("human"));
    }

    #[test]
    fn reject_cycle() {
        let mut dag = IncrementalTopo::new();

        dag.add_node("1");
        dag.add_node("2");
        dag.add_node("3");

        assert_eq!(dag.size(), 3);

        assert!(dag.add_dependency("1", "2").is_ok());
        assert!(dag.add_dependency("2", "3").is_ok());

        assert!(dag.add_dependency("3", "1").is_err());
        assert!(dag.add_dependency("1", "1").is_err());
    }

    #[test]
    fn get_children_unordered() {
        let dag = get_basic_dag().unwrap();

        let children: HashSet<_> = dag
            .descendants_unsorted("human")
            .unwrap()
            .map(|(_, v)| *v)
            .collect();

        let mut expected_children = HashSet::new();
        expected_children.extend(vec!["dog", "cat", "mouse", "grass"]);

        assert_eq!(children, expected_children);

        let ordered_children: Vec<_> = dag.descendants("human").unwrap().map(|v| *v).collect();
        assert_eq!(ordered_children, vec!["dog", "cat", "mouse", "grass"])
    }

    #[test]
    fn topo_order_values_no_gaps() {
        let dag = get_basic_dag().unwrap();

        let topo_orders: HashSet<_> = dag
            .descendants_unsorted("lion")
            .unwrap()
            .map(|p| p.0)
            .collect();

        assert_eq!(topo_orders, (2..=7).collect::<HashSet<_>>())
    }

    #[test]
    fn readme_example() {
        let mut dag = IncrementalTopo::new();

        dag.add_node("cat");
        dag.add_node("dog");
        dag.add_node("human");

        assert_eq!(dag.size(), 3);

        dag.add_dependency("human", "dog").unwrap();
        dag.add_dependency("human", "cat").unwrap();
        dag.add_dependency("dog", "cat").unwrap();

        let animal_order: Vec<_> = dag.descendants("human").unwrap().map(|v| *v).collect();

        assert_eq!(animal_order, vec!["dog", "cat"]);
    }

    #[test]
    fn unordered_iter() {
        let mut dag = IncrementalTopo::new();

        assert!(dag.add_node("cat"));
        assert!(dag.add_node("mouse"));
        assert!(dag.add_node("dog"));
        assert!(dag.add_node("human"));

        assert!(dag.add_dependency("human", "cat").unwrap());
        assert!(dag.add_dependency("human", "dog").unwrap());
        assert!(dag.add_dependency("dog", "cat").unwrap());
        assert!(dag.add_dependency("cat", "mouse").unwrap());

        let pairs = dag
            .descendants_unsorted("human")
            .unwrap()
            .collect::<HashSet<_>>();

        let mut expected_pairs = HashSet::new();
        expected_pairs.extend(vec![(2, &"dog"), (3, &"cat"), (4, &"mouse")]);

        assert_eq!(pairs, expected_pairs);
    }

    #[test]
    fn topo_cmp() {
        use std::cmp::Ordering::*;
        let mut dag = IncrementalTopo::new();

        assert!(dag.add_node("cat"));
        assert!(dag.add_node("mouse"));
        assert!(dag.add_node("dog"));
        assert!(dag.add_node("human"));

        assert!(dag.add_dependency("human", "cat").unwrap());
        assert!(dag.add_dependency("human", "dog").unwrap());
        assert!(dag.add_dependency("dog", "cat").unwrap());
        assert!(dag.add_dependency("cat", "mouse").unwrap());

        assert_eq!(dag.topo_cmp("human", "mouse").unwrap(), Less);
        assert_eq!(dag.topo_cmp("cat", "dog").unwrap(), Greater);
        assert!(dag.topo_cmp("cat", "horse").is_err());
    }
}
