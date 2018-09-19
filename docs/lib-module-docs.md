The purpose of this crate is to maintain an topological order in the face of single updates, like adding new nodes, adding new depedencies, deleting dependencies, and deleting nodes.

Adding nodes, deleting nodes, and deleting dependencies require a trivial amount of work to perform an update, because those operations do not change the topological ordering. Adding new dependencies does

## What is a Topological Order

To define a topological order requires at least simple definitions of a graph, and specifically a directed acyclic graph (DAG). A graph can be described as a pair of sets, `(V, E)` where `V` is the set of all nodes in the graph, and `E` is the set of edges. An edge is defined as a pair, `(m, n)` where `m` and `n` are nodes. A directed graph means that edges only imply a single direction of relationship between two nodes, as opposed to a undirected graph which implies the relationship goes both ways. An example of undirected vs. directed in social networks would be Facebook vs. Twitter. Facebook friendship is a two way relationship, while following someone on Twitter does not imply that they follow you back.

A topological ordering, `ord_D` of a directed acyclic graph, `D = (V, E)` where `x, y ∈ V`, is a mapping of nodes to priority values such that `ord_D(x) < ord_D(y)` holds for all edges `(x, y) ∈ E`. This yields a total ordering of the nodes in `D`.

## Examples

```
use incremental_topo::IncrementalTopo;
use std::collections::HashSet;
use std::cmp::Ordering::*;

let mut dag = IncrementalTopo::new();

dag.add_node("dog");
dag.add_node("cat");
dag.add_node("mouse");
dag.add_node("lion");
dag.add_node("human");
dag.add_node("gazelle");
dag.add_node("grass");

assert_eq!(dag.size(), 7);

dag.add_dependency("lion", "human").unwrap();
dag.add_dependency("lion", "gazelle").unwrap();

dag.add_dependency("human", "dog").unwrap();
dag.add_dependency("human", "cat").unwrap();

dag.add_dependency("dog", "cat").unwrap();
dag.add_dependency("cat", "mouse").unwrap();

dag.add_dependency("gazelle", "grass").unwrap();

dag.add_dependency("mouse", "grass").unwrap();

let pairs = dag.descendants_unsorted("human").unwrap().collect::<HashSet<_>>();
let expected_pairs = [(4, &"cat"), (3, &"dog"), (5, &"mouse"), (7, &"grass")].iter().cloned().collect::<HashSet<_>>();

assert_eq!(pairs, expected_pairs);

assert!(dag.contains_transitive_dependency("lion", "grass"));
assert!(!dag.contains_transitive_dependency("human", "gazelle"));

assert_eq!(dag.topo_cmp("cat", "dog").unwrap(), Greater);
assert_eq!(dag.topo_cmp("lion", "human").unwrap(), Less);
```

## Sources

The [paper by D. J. Pearce and P. H. J. Kelly] contains descriptions of three different algorithms for incremental topological ordering, along with analysis of runtime bounds for each.

[paper by D. J. Pearce and P. H. J. Kelly]: http://www.doc.ic.ac.uk/~phjk/Publications/DynamicTopoSortAlg-JEA-07.pdf
