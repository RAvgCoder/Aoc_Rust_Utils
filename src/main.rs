use aoc_utils_rust::graph::{EdgeRelationship, StaticGraph};
use std::collections::HashMap;

fn main() {
    // Use graph.rs from HM<N, Vec<N>> to create a graph of integers to perform topological sort
    let mut input = HashMap::<i32, Vec<i32>>::new();
    input.insert(1, vec![2, 3]);
    input.insert(2, vec![3]);
    input.insert(3, vec![4]);
    input.insert(4, vec![]);

    let mut graph = StaticGraph::<_, ()>::from(input);
    let topologically_sorted = graph
        .topological_sort()
        .unwrap()
        .iter()
        .map(|node| *graph.get_node(*node).unwrap())
        .collect::<Vec<i32>>();

    // Create these inserts manually to test the graph
    // Graph: (4 nodes) {
    //     Node: (NodePtr { idx: 0 }) (Data: '2') : [
    //         Edge: '()' ->  Node: (NodePtr { idx: 1 }) (Data: '3')
    //     ]
    //     Node: (NodePtr { idx: 1 }) (Data: '3') : [
    //         Edge: '()' ->  Node: (NodePtr { idx: 2 }) (Data: '4')
    //     ]
    //     Node: (NodePtr { idx: 2 }) (Data: '4') : []
    //     Node: (NodePtr { idx: 3 }) (Data: '1') : [
    //         Edge: '()' ->  Node: (NodePtr { idx: 1 }) (Data: '3')
    //     Edge: '()' ->  Node: (NodePtr { idx: 0 }) (Data: '2')
    //     ]
    // }
    graph.add_node(2);
    graph.add_node(3);
    graph.add_node(4);
    graph.add_node(1);

    graph.add_edge_by_data(1, 2, EdgeRelationship::AToB(()));
    graph.add_edge_by_data(1, 3, EdgeRelationship::AToB(()));
    graph.add_edge_by_data(2, 3, EdgeRelationship::AToB(()));
    graph.add_edge_by_data(3, 4, EdgeRelationship::AToB(()));
    println!("{:?}", graph);
    graph
        .topological_sort()
        .unwrap()
        .iter()
        .for_each(|node| print!("{}, ", graph.get_node(*node).unwrap()));
}
