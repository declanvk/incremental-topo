#![feature(nll)]

extern crate failure;
#[macro_use]
extern crate failure_derive;
extern crate slab;

pub mod bimap;

use bimap::BiMap;
use slab::Slab;
use std::{
    borrow::Borrow,
    cmp::{Ordering, Reverse},
    collections::{BinaryHeap, HashSet},
    hash::Hash,
    iter::Iterator,
};

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

#[derive(Fail, Debug)]
pub enum Error {
    #[fail(display = "Node was not found in graph")]
    NodeMissing,
    #[fail(display = "Nodes may not transitively depend on themselves in a cyclic fashion")]
    CycleDetected,
}

pub type Result<T> = std::result::Result<T, Error>;

impl<T: Hash + Eq> IncrementalTopo<T> {
    pub fn new() -> Self {
        IncrementalTopo {
            node_keys: BiMap::new(),
            node_data: Slab::new(),
            last_topo_order: 0,
        }
    }

    pub fn add_node(&mut self, node: T) -> bool {
        if self.contains_node(&node) {
            return false;
        }

        let next_topo_order = self.last_topo_order + 1;
        let node_entry = self.node_data.vacant_entry();
        let key = node_entry.key();

        self.node_keys.insert(node, key);

        node_entry.insert(NodeData::new(next_topo_order));

        self.last_topo_order = next_topo_order;

        true
    }

    pub fn contains_node<Q>(&self, node: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.node_keys.contains_left(node)
    }

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

        // If the affected region of the graph has non-zero size (i.e. the upper and
        // lower bound are equal) then perform an update to the topological ordering of
        // the graph
        if lower_bound < upper_bound {
            let mut visited = HashSet::new();

            // Walk changes forward from the succ, checking for any cycles that would be
            // introduced
            let change_forward = self.dfs_forward(succ_key, &mut visited, upper_bound)?;
            // Walk backwards from the prec
            let change_backward = self.dfs_backward(prec_key, &mut visited, lower_bound);

            self.reorder_nodes(change_forward, change_backward);
        }

        Ok(true)
    }

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

        self.node_data[prec_key].children.remove(&succ_key);
        self.node_data[succ_key].parents.remove(&prec_key);

        true
    }

    pub fn size(&self) -> usize {
        self.node_keys.len()
    }

    pub fn iter(&self) -> bimap::Values<T> {
        self.node_keys.left_values()
    }

    pub fn iter_mut(&mut self) -> bimap::ValuesMut<T> {
        self.node_keys.left_values_mut()
    }

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

        stack.push(node_key);

        Ok(DescendantsUnsorted {
            dag: self,
            stack,
            visited,
        })
    }

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

        let order = self.node_data[node_key].topo_order;

        let mut queue = BinaryHeap::new();

        queue.push((Reverse(order), node_key));

        let visited = HashSet::new();

        Ok(Descendants {
            dag: self,
            queue,
            visited,
        })
    }

    pub fn topo_cmp<Q, R>(&self, prec: &Q, succ: &R) -> Result<Ordering>
    where
        T: Borrow<Q> + Borrow<R>,
        Q: Hash + Eq + ?Sized,
        R: Hash + Eq + ?Sized,
    {
        let (prec_key, succ_key) = self.get_dep_keys(prec, succ)?;

        Ok(self.node_data[prec_key]
            .topo_order
            .cmp(&self.node_data[succ_key].topo_order))
    }

    pub fn topo_order<Q>(&self, node: &Q) -> Result<u32>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let node_key = *self.node_keys.get_by_left(node).ok_or(Error::NodeMissing)?;

        Ok(self.node_data[node_key].topo_order)
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

        for (key, topo_order) in change_forward {
            all_keys.push(key);
            all_topo_orders.push(topo_order);
        }

        for (key, topo_order) in change_backward {
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
        loop {
            if let Some(key) = self.stack.pop() {
                if self.visited.contains(&key) {
                    continue;
                } else {
                    self.visited.insert(key);
                }

                let node = self.dag.node_keys.get_by_right(&key).unwrap();
                let order = self.dag.node_data[key].topo_order;

                self.stack.extend(&self.dag.node_data[key].children);

                return Some((order, node));
            } else {
                return None;
            }
        }
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
        expected_children.extend(vec!["human", "dog", "cat", "mouse", "grass"]);

        assert_eq!(children, expected_children);

        let ordered_children: Vec<_> = dag.descendants("human").unwrap().map(|v| *v).collect();
        assert_eq!(
            ordered_children,
            vec!["human", "dog", "cat", "mouse", "grass"]
        )
    }

    #[test]
    fn topo_order_values_no_gaps() {
        let dag = get_basic_dag().unwrap();

        let topo_orders: HashSet<_> = dag
            .descendants_unsorted("lion")
            .unwrap()
            .map(|p| p.0)
            .collect();

        assert_eq!(topo_orders, (1..=7).collect::<HashSet<_>>())
    }

    #[test]
    fn readme_example() {
        let mut dag = IncrementalTopo::new();

        dag.add_node("dog");
        dag.add_node("cat");
        dag.add_node("human");

        assert_eq!(dag.size(), 3);

        dag.add_dependency("human", "dog").unwrap();
        dag.add_dependency("human", "cat").unwrap();
        dag.add_dependency("dog", "cat").unwrap();

        let animal_order: Vec<_> = dag.descendants("human").unwrap().map(|v| *v).collect();

        assert_eq!(animal_order, vec!["human", "dog", "cat"]);
    }
}
