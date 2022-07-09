#[macro_use]
extern crate criterion;
extern crate incremental_topo;
extern crate rand;

use criterion::{BatchSize, BenchmarkId, Criterion};
use incremental_topo::IncrementalTopo;

const DEFAULT_DENSITY: f32 = 0.1;
const DEFAULT_SIZE: u64 = 1000;

fn generate_random_dag(size: u64, density: f32) -> IncrementalTopo<u64> {
    use rand::distributions::{Bernoulli, Distribution};
    assert!(0.0 < density && density <= 1.0);
    let mut rng = rand::thread_rng();
    let dist = Bernoulli::new(density.into()).unwrap();
    let mut topo = IncrementalTopo::new();

    for node in 0..size {
        topo.add_node(node);
    }

    for i in 0..size {
        for j in 0..size {
            if i != j && dist.sample(&mut rng) {
                // Ignore failures
                let _ = topo.add_dependency(&i, &j);
            }
        }
    }

    topo
}

fn criterion_benchmark(c: &mut Criterion) {
    use rand::distributions::{Distribution, Uniform};

    let mut random_graph_different_density_group =
        c.benchmark_group("random_graph_different_density");

    for density in [0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09, 0.1] {
        random_graph_different_density_group.bench_with_input(
            criterion::BenchmarkId::new("single_insert", density),
            &density,
            |b, &density| {
                let dag = generate_random_dag(750, density);
                let mut rng = rand::thread_rng();
                let dist = Uniform::new(0, 750);

                b.iter_batched(
                    || {
                        let i = dist.sample(&mut rng);
                        let j = dist.sample(&mut rng);
                        let dag = dag.clone();

                        (i, j, dag)
                    },
                    |(i, j, mut dag)| {
                        let _ = dag.add_dependency(&i, &j);
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    for density in [0.02, 0.04, 0.06, 0.08, 0.1] {
        random_graph_different_density_group.bench_with_input(
            BenchmarkId::new("contains_dependency", density),
            &density,
            |b, &density| {
                let dag = generate_random_dag(DEFAULT_SIZE, density);
                let mut rng = rand::thread_rng();
                let dist = Uniform::new(0, DEFAULT_SIZE);

                b.iter_batched(
                    || {
                        let i = dist.sample(&mut rng);
                        let j = dist.sample(&mut rng);

                        (i, j)
                    },
                    |(i, j)| {
                        let _ = dag.contains_dependency(&i, &j);
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    random_graph_different_density_group.finish();

    c.bench_function("clone", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter(|| dag.clone());
    });

    c.bench_function("contains_node", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter_batched_ref(
            || dag.clone(),
            |dag| {
                dag.contains_node(&500);
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("delete_node", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter_batched(
            || dag.clone(),
            |mut dag| dag.delete_node(&500),
            BatchSize::SmallInput,
        );
    });

    c.bench_function("contains_transitive_dependency", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);
        let mut rng = rand::thread_rng();
        let dist = Uniform::new(0, DEFAULT_SIZE);

        b.iter_batched(
            || {
                let i = dist.sample(&mut rng);
                let j = dist.sample(&mut rng);

                (i, j)
            },
            |(i, j)| {
                let _ = dag.contains_transitive_dependency(&i, &j);
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("delete_dependency", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);
        let mut rng = rand::thread_rng();
        let dist = Uniform::new(0, DEFAULT_SIZE);

        b.iter_batched(
            || {
                let i = dist.sample(&mut rng);
                let j = dist.sample(&mut rng);
                let dag = dag.clone();

                (i, j, dag)
            },
            |(i, j, mut dag)| {
                let _ = dag.delete_dependency(&i, &j);
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("descendants_unsorted", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);
        let mut rng = rand::thread_rng();
        let dist = Uniform::new(0, DEFAULT_SIZE);

        b.iter_batched(
            || dist.sample(&mut rng),
            |i| {
                dag.descendants_unsorted(&i).unwrap().for_each(|v| drop(v));
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("descendants", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);
        let mut rng = rand::thread_rng();
        let dist = Uniform::new(0, DEFAULT_SIZE);

        b.iter_batched(
            || dist.sample(&mut rng),
            |i| {
                dag.descendants(&i).unwrap().for_each(|v| drop(v));
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("topo_cmp", |b| {
        let dag = generate_random_dag(DEFAULT_SIZE, DEFAULT_DENSITY);
        let mut rng = rand::thread_rng();
        let dist = Uniform::new(0, DEFAULT_SIZE);

        b.iter_batched(
            || {
                let i = dist.sample(&mut rng);
                let j = dist.sample(&mut rng);

                (i, j)
            },
            |(i, j)| {
                let _ = dag.topo_cmp(&i, &j).unwrap();
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
