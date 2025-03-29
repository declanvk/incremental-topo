use incremental_topo::IncrementalTopo;

#[test]
fn readme_contents() {
    let mut dag = IncrementalTopo::new();

    let cat = dag.add_node();
    let dog = dag.add_node();
    let human = dag.add_node();

    assert_eq!(dag.len(), 3);

    dag.add_dependency(human, dog).unwrap();
    dag.add_dependency(human, cat).unwrap();
    dag.add_dependency(dog, cat).unwrap();

    let animal_order: Vec<_> = dag.descendants(human).unwrap().collect();

    assert_eq!(animal_order, vec![dog, cat]);
}
