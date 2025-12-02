pub mod coordinate_system;
pub mod day_setup;
pub mod graph;
pub mod grid;
pub mod math;
pub mod miscellaneous;

#[cfg(test)]
mod test {
    #[test]
    fn test() {

        use crate::graph::{EdgeRelationship, StaticGraph};
        let mut graph = StaticGraph::new();

        let a = graph.add_node("A");
        let b = graph.add_node("B");
        let c = graph.add_node("C");
        let d = graph.add_node("D");
        let e = graph.add_node("E");
        let f = graph.add_node("F");

        graph
            .add_edge(
                e,
                f,
                EdgeRelationship::BiDirectional {
                    a_to_b: 33,
                    b_to_a: 33,
                },
            )
            .unwrap();
        graph
            .add_edge(
                e,
                d,
                EdgeRelationship::BiDirectional {
                    a_to_b: 18,
                    b_to_a: 18,
                },
            )
            .unwrap();
        graph
            .add_edge(
                e,
                c,
                EdgeRelationship::BiDirectional {
                    a_to_b: 2,
                    b_to_a: 2,
                },
            )
            .unwrap();

        graph
            .add_edge(
                f,
                d,
                EdgeRelationship::BiDirectional {
                    a_to_b: 9,
                    b_to_a: 9,
                },
            )
            .unwrap();
        graph
            .add_edge(
                f,
                a,
                EdgeRelationship::BiDirectional {
                    a_to_b: 20,
                    b_to_a: 20,
                },
            )
            .unwrap();
        graph
            .add_edge(
                f,
                b,
                EdgeRelationship::BiDirectional {
                    a_to_b: 38,
                    b_to_a: 38,
                },
            )
            .unwrap();

        graph
            .add_edge(
                d,
                c,
                EdgeRelationship::BiDirectional {
                    a_to_b: 7,
                    b_to_a: 7,
                },
            )
            .unwrap();
        graph
            .add_edge(
                d,
                b,
                EdgeRelationship::BiDirectional {
                    a_to_b: 5,
                    b_to_a: 5,
                },
            )
            .unwrap();

        graph
            .add_edge(
                a,
                c,
                EdgeRelationship::BiDirectional {
                    a_to_b: 12,
                    b_to_a: 12,
                },
            )
            .unwrap();
        graph
            .add_edge(
                a,
                b,
                EdgeRelationship::BiDirectional {
                    a_to_b: 19,
                    b_to_a: 19,
                },
            )
            .unwrap();

        graph
            .add_edge(
                c,
                b,
                EdgeRelationship::BiDirectional {
                    a_to_b: 15,
                    b_to_a: 15,
                },
            )
            .unwrap();

        // Apply Kruskal's algorithm to find the MST
        let mst = graph.kruskal();

        // Print the edges of the MST
        let result = mst
            .into_iter()
            .map(|e_ptr| {
                let (from, to) = graph
                    .get_edge_connection(e_ptr)
                    .expect("Edge should exist.");
                (
                    *graph.get_edge(e_ptr).expect("Edge should exist."),
                    (
                        graph.get_node(from).expect("Node should exist."),
                        graph.get_node(to).expect("Node should exist."),
                    ),
                )
            })
            .collect::<Vec<_>>();

        // Expected result
        // 2 -- 3 == 4
        // 0 -- 3 == 5
        // 0 -- 1 == 10

        for (edge, (from, to)) in result {
            println!("{:?}", (edge, (from, to)));
            // println!("{} -- {} == {}", from, to, edge);
        }
    }
}
