#[macro_use]
extern crate criterion;
extern crate incremental_topo;
extern crate rand;

use criterion::Criterion;

use incremental_topo::IncrementalTopo;

fn generate_random_dag(size: u64, density: f32) -> IncrementalTopo<u64> {
    use rand::distributions::{Bernoulli, Distribution};
    assert!(0.0 < density && density <= 1.0);
    let mut rng = rand::thread_rng();
    let dist = Bernoulli::new(density.into());
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
    c.bench_function_over_inputs(
        "single_insert_random_graph_different_density",
        |b, &&density| {
            let dag = generate_random_dag(750, density);
            let mut rng = rand::thread_rng();
            let dist = Uniform::new(0, 750);

            let i = dist.sample(&mut rng);
            let j = dist.sample(&mut rng);

            b.iter(|| {
                let mut dag = dag.clone();
                let _ = dag.add_dependency(&i, &j);
            });
        },
        &[0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09, 0.1],
    );

    c.bench_function_over_inputs(
        "random_graph_clone",
        |b, &&density| {
            let dag = generate_random_dag(1000, density);

            b.iter(|| dag.clone());
        },
        &[0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09, 0.1],
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
