use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use criterion_perf_events::Perf;
use incremental_topo::{self as topo, IncrementalTopo};
use perfcnt::linux::{HardwareEventType, PerfCounterBuilderLinux};
use rand::{
    distributions::Distribution,
    prelude::{SliceRandom, ThreadRng},
};

const DEFAULT_DENSITY: f32 = 0.1;
const DEFAULT_SIZE: u64 = 1000;

fn generate_random_dag(
    rng: &mut ThreadRng,
    size: u64,
    density: f32,
) -> (Vec<topo::Node>, IncrementalTopo) {
    use rand::distributions::Bernoulli;

    assert!(0.0 < density && density <= 1.0);
    let dist = Bernoulli::new(density.into()).unwrap();
    let mut topo = IncrementalTopo::new();

    let nodes: Vec<_> = (0..size).map(|_| topo.add_node()).collect();

    for i in nodes.iter() {
        for j in nodes.iter() {
            if i != j && dist.sample(rng) {
                // Ignore failures
                let _ = topo.add_dependency(i, j);
            }
        }
    }

    (nodes, topo)
}

fn criterion_benchmark(c: &mut Criterion<Perf>) {
    let mut rng = rand::thread_rng();

    let mut mutate_graph_group = c.benchmark_group("mutate_graph");

    for density in [0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09, 0.1] {
        let (nodes, dag) = generate_random_dag(&mut rng, 750, density);

        mutate_graph_group.bench_with_input(
            criterion::BenchmarkId::new("add_dependency", density),
            &density,
            |b, _| {
                b.iter_batched(
                    || {
                        let i = nodes.choose(&mut rng).unwrap();
                        let j = nodes.choose(&mut rng).unwrap();
                        let dag = dag.clone();

                        (i, j, dag)
                    },
                    |(i, j, mut dag)| dag.add_dependency(i, j),
                    BatchSize::SmallInput,
                );
            },
        );

        mutate_graph_group.bench_with_input(
            BenchmarkId::new("delete_node", density),
            &density,
            |b, _| {
                b.iter_batched(
                    || dag.clone(),
                    |mut dag| dag.delete_node(nodes[500]),
                    BatchSize::SmallInput,
                );
            },
        );

        mutate_graph_group.bench_with_input(
            BenchmarkId::new("delete_dependency", density),
            &density,
            |b, _| {
                b.iter_batched(
                    || {
                        let i = nodes.choose(&mut rng).unwrap();
                        let j = nodes.choose(&mut rng).unwrap();
                        let dag = dag.clone();

                        (i, j, dag)
                    },
                    |(i, j, mut dag)| dag.delete_dependency(i, j),
                    BatchSize::SmallInput,
                );
            },
        );
    }

    mutate_graph_group.finish();

    let mut query_graph_group = c.benchmark_group("query_graph");

    for density in [0.02, 0.04, 0.06, 0.08, 0.1] {
        let (nodes, dag) = generate_random_dag(&mut rng, DEFAULT_SIZE, density);

        query_graph_group.bench_with_input(
            BenchmarkId::new("contains_dependency", density),
            &density,
            |b, _| {
                b.iter_batched(
                    || {
                        let i = nodes.choose(&mut rng).unwrap();
                        let j = nodes.choose(&mut rng).unwrap();

                        (i, j)
                    },
                    |(i, j)| dag.contains_dependency(i, j),
                    BatchSize::SmallInput,
                );
            },
        );

        query_graph_group.bench_with_input(
            BenchmarkId::new("contains_node", density),
            &density,
            |b, _| {
                b.iter(|| dag.contains_node(nodes[500]));
            },
        );

        query_graph_group.bench_with_input(
            BenchmarkId::new("contains_transitive_dependency", density),
            &density,
            |b, _| {
                b.iter_batched(
                    || {
                        let i = nodes.choose(&mut rng).unwrap();
                        let j = nodes.choose(&mut rng).unwrap();

                        (i, j)
                    },
                    |(i, j)| dag.contains_transitive_dependency(i, j),
                    BatchSize::SmallInput,
                );
            },
        );
    }

    query_graph_group.finish();

    c.bench_function("clone", |b| {
        let dag = generate_random_dag(&mut rng, DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter(|| dag.clone());
    });

    c.bench_function("descendants_unsorted", |b| {
        let (nodes, dag) = generate_random_dag(&mut rng, DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter_batched(
            || nodes.choose(&mut rng).unwrap(),
            |i| {
                dag.descendants_unsorted(i).unwrap().for_each(|v| drop(v));
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("descendants", |b| {
        let (nodes, dag) = generate_random_dag(&mut rng, DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter_batched(
            || nodes.choose(&mut rng).unwrap(),
            |i| {
                dag.descendants(i).unwrap().for_each(|v| drop(v));
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("topo_cmp", |b| {
        let (nodes, dag) = generate_random_dag(&mut rng, DEFAULT_SIZE, DEFAULT_DENSITY);

        b.iter_batched(
            || {
                let i = nodes.choose(&mut rng).unwrap();
                let j = nodes.choose(&mut rng).unwrap();

                (i, j)
            },
            |(i, j)| dag.topo_cmp(i, j),
            BatchSize::SmallInput,
        );
    });
}

fn create_criterion_configuration() -> Criterion<Perf> {
    Criterion::default().with_measurement(Perf::new(PerfCounterBuilderLinux::from_hardware_event(
        HardwareEventType::Instructions,
    )))
}

criterion_group! {
    name = benches;
    config = create_criterion_configuration();
    targets = criterion_benchmark
}
criterion_main!(benches);
