# Incremental Topo

[![Crates.io](https://img.shields.io/crates/v/incremental-topo.svg)](https://crates.io/crates/incremental-topo)
[![Travis CI](https://travis-ci.org/declanvk/incremental-topo.svg?branch=master)](https://travis-ci.org/declanvk/incremental-topo)
[![Documentation](https://docs.rs/incremental-topo/badge.svg)](https://docs.rs/incremental-topo)

A data structure for maintaining an topological ordering in an incremental fashion.

## Usage

To use `incremental-topo`, first add this to your `Cargo.toml`:

```toml
[dependencies]
incremental-topo = "0.1"
```

Next, add this to your crate:

```rust
extern crate incremental_topo;

use incremental_topo::IncrTopo;

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
```

See [documentation](https://docs.rs/incremental-topo) for more details.

## License

This project is dual licensed under the [MIT license](LICENSE-MIT) and [Apache 2.0 license](LICENSE-APACHE).
