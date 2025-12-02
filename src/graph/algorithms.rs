use crate::graph::algorithms::union_find::UnionFind;
use crate::graph::{StaticEdgePtr, StaticGraph, StaticNodePtr};

/// Algorithms
impl<N, E> StaticGraph<N, E> {
    /// Performs a topological sort on the graph.
    ///
    /// This function returns a vector of `NodePtr` representing the nodes in topologically sorted order.
    /// If the graph contains a cycle, it returns a unit `Err`.
    ///
    /// # Examples
    ///
    /// ### Without cycles
    /// ```
    ///  use std::collections::HashMap;
    ///  use aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    ///  let mut input = HashMap::<i32, Vec<i32>>::new();
    ///  input.insert(1, vec![2, 3]);
    ///  input.insert(2, vec![3]);
    ///  input.insert(3, vec![4]);
    ///  input.insert(4, vec![]);
    ///
    ///  let mut graph = StaticGraph::<_, ()>::from(input);
    ///
    ///  let topologically_sorted = graph
    ///         .topological_sort()
    ///         .expect("This graph does not contain cycles and is therefore topologically sortable.")
    ///         .iter()
    ///         .map(|node: &StaticNodePtr| *graph.get_node(*node).expect("Node should exist as it was returned by topological_sort."))
    ///         .collect::<Vec<i32>>();
    ///
    ///  assert_eq!(topologically_sorted, vec![1, 2, 3, 4]);
    /// ```
    ///
    /// ### With cycles
    /// ```
    /// use aoc_utils_rust::graph::{StaticGraph, StaticNodePtr, EdgeRelationship};
    ///
    /// let mut graph = StaticGraph::new();
    /// let node_a = graph.add_node("A");
    /// let node_b = graph.add_node("B");
    /// let node_c = graph.add_node("C");
    /// graph.add_edge(node_a, node_b, EdgeRelationship::AToB(())).unwrap();
    /// graph.add_edge(node_b, node_c, EdgeRelationship::AToB(())).unwrap();
    /// graph.add_edge(node_c, node_a, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let sorted = graph.topological_sort();
    /// assert!(sorted.is_err());
    /// ```
    pub fn topological_sort(&self) -> Result<Vec<StaticNodePtr>, ()> {
        let mut result = Vec::with_capacity(self.nodes.len());
        let mut zero_in_degree_nodes = Vec::new();

        let mut in_degrees = self.get_in_degrees();

        // Collect nodes with zero in-degree
        for (node_ptr, in_degree) in in_degrees.iter() {
            if *in_degree == 0 {
                zero_in_degree_nodes.push(*node_ptr);
            }
        }
        
        // Process nodes with zero in-degree
        while let Some(node) = zero_in_degree_nodes.pop() {
            result.push(node);

            for (neighbour, _) in self.neighbours_iter(node) {
                let degree = &mut in_degrees[neighbour.idx].1;
                *degree -= 1;
                if *degree == 0 {
                    zero_in_degree_nodes.push(neighbour);
                }
            }
        }

        // Check if all nodes are processed
        if result.len() == in_degrees.len() {
            Ok(result)
        } else {
            Err(()) // Cycle detected
        }
    }

    /// Performs Kruskal's algorithm to find the Minimum Spanning Tree (MST) of the graph.
    ///
    /// # Type Parameters
    /// - `E`: The type of the data associated with each edge. It must implement the `Ord` trait
    ///   to allow sorting the edges by their weight.
    ///
    /// # Returns
    /// Returns a vector of `StaticEdgePtr` representing the edges that form the Minimum Spanning Tree (MST).
    ///
    /// # Example
    /// ```
    ///  use crate::aoc_utils_rust::graph::{EdgeRelationship, StaticGraph };
    ///  let mut graph = StaticGraph::new();
    ///     
    ///  let a = graph.add_node("A");
    ///  let b = graph.add_node("B");
    ///  let c = graph.add_node("C");
    ///  let d = graph.add_node("D");
    ///  let e = graph.add_node("E");
    ///  let f = graph.add_node("F");
    ///  
    ///  graph.add_edge(e, f, EdgeRelationship::BiDirectional {a_to_b: 33, b_to_a: 33}).unwrap();
    ///  graph.add_edge(e, d, EdgeRelationship::BiDirectional {a_to_b: 18, b_to_a: 18}).unwrap();
    ///  graph.add_edge(e, c, EdgeRelationship::BiDirectional {a_to_b: 2, b_to_a: 2}).unwrap();
    ///  
    ///  graph.add_edge(f, d, EdgeRelationship::BiDirectional {a_to_b: 9, b_to_a: 9}).unwrap();
    ///  graph.add_edge(f, a, EdgeRelationship::BiDirectional {a_to_b: 20, b_to_a: 20}).unwrap();
    ///  graph.add_edge(f, b, EdgeRelationship::BiDirectional {a_to_b: 38, b_to_a: 38}).unwrap();
    ///  
    ///  graph.add_edge(d, c, EdgeRelationship::BiDirectional {a_to_b: 7, b_to_a: 7}).unwrap();
    ///  graph.add_edge(d, b, EdgeRelationship::BiDirectional {a_to_b: 5, b_to_a: 5}).unwrap();
    ///  
    ///  graph.add_edge(a, c, EdgeRelationship::BiDirectional {a_to_b: 12, b_to_a: 12}).unwrap();
    ///  graph.add_edge(a, b, EdgeRelationship::BiDirectional {a_to_b: 19, b_to_a: 19}).unwrap();
    ///  
    ///  graph.add_edge(c, b, EdgeRelationship::BiDirectional {a_to_b: 15, b_to_a: 15}).unwrap();
    ///  
    ///  
    ///  // Apply Kruskal's algorithm to find the MST
    ///  let mst = graph.kruskal();
    ///  
    ///  // Print the edges of the MST
    ///  let result = mst
    ///  .into_iter()
    ///  .map(|e_ptr| {
    ///       let (from, to) = graph.get_edge_connection(e_ptr).expect("Edge should exist.");
    ///       (
    ///            *graph.get_edge(e_ptr).expect("Edge should exist."),
    ///            (
    ///                *graph.get_node(from).expect("Node should exist."),
    ///                *graph.get_node(to).expect("Node should exist."),
    ///            ),
    ///       )
    ///  })
    ///  .collect::<Vec<_>>();
    ///
    ///  // Expected result
    ///  let expected = [
    ///     (2, ("E", "C")),
    ///     (5, ("D", "B")),
    ///     (7, ("D", "C")),
    ///     (9, ("F", "D")),
    ///     (12, ("A", "C")),
    ///  ];
    ///
    /// assert_eq!(result, expected);
    /// ```
    ///
    /// # Algorithm Description
    /// - **Step 1**: Sort all the edges by their weight in ascending order.
    /// - **Step 2**: Initialize a union-find data structure to keep track of connected components.
    /// - **Step 3**: Process each edge in sorted order, adding it to the MST if it connects two previously unconnected components.
    /// - **Step 4**: Return the edges included in the MST.
    pub fn kruskal(&self) -> Vec<StaticEdgePtr>
    where
        E: Ord,
    {
        let mut edges = self.edges.iter().enumerate().collect::<Vec<_>>();
        // Sort edges by weight in ascending order
        edges.sort_by_key(|(_, edge)| &edge.data);
        
        let mut result = Vec::new();
        let mut uf = UnionFind::new(self);

        // Iterate over sorted edges
        for (edge_idx, edge) in edges {
            let (from, to) = (edge.holder, edge.to);
            if uf.union(from, to).is_ok() {
                result.push(StaticEdgePtr { idx: edge_idx });
            }
        }

        result
    }
}
/// The `union_find` module implements the **Union-Find** or **Disjoint Set Union (DSU)** data structure,
/// which efficiently supports the operations of **union** and **find** to handle the merging and querying
/// of disjoint sets. This data structure is commonly used in algorithms involving connected components
/// and graph traversal.
///
/// This implementation uses **path compression** for efficient find operations and **union by size**
/// for efficient union operations, ensuring that the union-find structure remains balanced and optimized
/// for large datasets.

pub mod union_find {
    use crate::graph::{StaticGraph, StaticNodePtr};
    use std::collections::HashMap;
    use std::fmt;
    use std::fmt::Debug;
    use std::marker::PhantomData;

    /// Errors that can occur during union-find operations.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum UnionFindError {
        /// This error occurs when attempting to union two nodes that are already in the same set.
        NodesInSameGroup,

        /// This error occurs when the nodes being queried do not belong to the same graph.
        NodesNotFromSameGraph,
    }

    /// A structure representing a Union-Find data structure.
    ///
    /// It stores the parent and size of each node in the disjoint sets, enabling efficient union and find operations.
    #[derive(Clone)]
    pub struct UnionFind<'graph> {
        /// A vector where each element represents the parent of a node.
        /// If an element is equal to its own index, it is a root node.
        parent: Vec<StaticNodePtr>,

        /// A vector where each element represents the size of the group rooted at the corresponding index.
        /// Only valid for group roots.
        group_size: Vec<usize>,

        /// A phantom data field to ensure that the UnionFind structure is tied to a specific graph.
        /// This prevents modification of the graph while the UnionFind structure is in use.
        _graph_lock: PhantomData<&'graph ()>,
    }

    /// A structure representing the root of a group and its size.
    #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
    pub struct GroupRoot {
        /// The index of the root of the group.
        pub ptr: StaticNodePtr,

        /// The size of the group.
        pub size: usize,
    }

    impl<'graph> UnionFind<'graph> {
        /// Creates a new `UnionFind` structure with the given number of nodes.
        ///
        /// Initially, each node is its own root, and the group size is 0 for all nodes.
        ///
        /// # Arguments
        /// * `size` - The number of nodes in the Union-Find structure.
        ///
        /// # Example
        ///```rust
        /// use aoc_utils_rust::graph::algorithms::union_find::{GroupRoot, UnionFind};
        /// use aoc_utils_rust::graph::StaticGraph;
        ///
        /// let mut graph: StaticGraph<_, ()> = StaticGraph::new();
        /// let nodea = graph.add_node("A");
        /// let nodeb = graph.add_node("B");
        /// let nodec = graph.add_node("C");
        ///
        /// let mut uf = UnionFind::new(&graph);
        /// let root = uf.find(nodea).expect("Node should exist.");
        /// assert_eq!(root, GroupRoot { ptr: nodea, size: 1 }); // Node 0 is its own root initially.
        /// ```
        pub fn new<N, E>(static_graph: &'graph StaticGraph<N, E>) -> Self {
            let size = static_graph.nodes.len();
            Self {
                parent: (0..size).map(|e| StaticNodePtr { idx: e }).collect(),
                group_size: vec![1; size],
                _graph_lock: PhantomData,
            }
        }

        /// Finds the root of the group containing the given node, with path compression.
        ///
        /// This method uses path compression to optimize future queries by making nodes point directly
        /// to the root of their group.
        ///
        /// # Arguments
        /// * `node` - A node whose group root is to be found.
        ///
        /// # Returns
        /// `Some(GroupRoot)` if the node is valid, and `None` if the node is invalid.
        ///
        /// # Example
        /// ```rust
        /// use aoc_utils_rust::graph::{EdgeRelationship, StaticGraph};
        /// use aoc_utils_rust::graph::algorithms::union_find::{GroupRoot, UnionFind};
        ///
        /// let mut graph = StaticGraph::new();
        ///
        /// let nodea = graph.add_node("A");
        /// let nodeb = graph.add_node("B");
        /// let nodec = graph.add_node("C");
        ///
        /// let noded = graph.add_node("d");
        /// let nodee = graph.add_node("e");
        /// let nodef = graph.add_node("f");
        /// let nodeg = graph.add_node("g");
        ///
        /// graph.add_edge(noded, nodee, EdgeRelationship::AToB(())).unwrap();
        /// graph.add_edge(nodeg, nodef, EdgeRelationship::AToB(())).unwrap();
        ///
        /// let mut uf = UnionFind::new(&graph);
        ///
        /// assert_eq!(uf.find(nodea).expect("Node should exist."), GroupRoot { ptr: nodea, size: 1 }); // Node A is its own root initially.
        /// assert_eq!(uf.find(nodeb).expect("Node should exist."), GroupRoot { ptr: nodeb, size: 1 }); // Node B is its own root initially.
        /// assert_eq!(uf.find(nodec).expect("Node should exist."), GroupRoot { ptr: nodec, size: 1 }); // Node C is its own root initially.
        ///
        /// uf.union(noded, nodee).unwrap();
        /// uf.union(nodeg, nodef).unwrap();
        ///
        /// assert_eq!(uf.find(noded).expect("Node should exist."), GroupRoot { ptr: noded, size: 2 }); // Node D is the root of {D, E}.
        /// assert_eq!(uf.find(nodee).expect("Node should exist."), GroupRoot { ptr: noded, size: 2 }); // Node E is in the group {D, E}.
        ///
        /// assert_eq!(uf.find(nodeg).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 2 }); // Node G is the root of {G, F}.
        /// assert_eq!(uf.find(nodef).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 2 }); // Node F is in the group {G, F}.
        /// ```
        pub fn find(&mut self, node: StaticNodePtr) -> Option<GroupRoot> {
            // If the node is its own parent, it is the root of the group.
            if *self.parent.get(*node)? == node {
                return Some(GroupRoot {
                    ptr: StaticNodePtr { idx: *node },
                    size: self.group_size[node.idx],
                });
            }

            // Recursively find the root with path compression.
            let parent = self.find(StaticNodePtr {
                idx: *self.parent[*node],
            })?;

            self.parent[node.idx] = parent.ptr; // Path compression
            Some(parent)
        }

        /// Unites the groups containing two nodes.
        ///
        /// This method merges the two sets into one. The smaller group is attached under the larger group,
        /// ensuring the resulting tree remains balanced.
        ///
        /// # Arguments
        /// * `node_a` - The first node to unite.
        /// * `node_b` - The second node to unite.
        ///
        /// # Returns
        /// Returns `Ok(())` if the union is successful, or a `UnionFindError` if the nodes are already
        /// in the same group or if the nodes belong to different graphs.
        ///
        /// # Example
        /// ```rust
        /// use aoc_utils_rust::graph::{EdgeRelationship, StaticGraph};
        /// use aoc_utils_rust::graph::algorithms::union_find::{GroupRoot, UnionFind, UnionFindError};
        ///
        /// let mut graph = StaticGraph::<_, ()>::new();
        ///
        /// let nodea = graph.add_node("A"); // idx: 0
        /// let nodeb = graph.add_node("B"); // idx: 1
        /// let nodec = graph.add_node("C"); // idx: 2
        /// let noded = graph.add_node("d"); // idx: 3
        /// let nodee = graph.add_node("e"); // idx: 4
        /// let nodef = graph.add_node("f"); // idx: 5
        /// let nodeg = graph.add_node("g"); // idx: 6
        ///
        /// let mut uf = UnionFind::new(&graph);
        /// assert_eq!(uf.count_groups(), 7);
        ///
        /// assert_eq!(uf.find(nodea).expect("Node should exist."), GroupRoot { ptr: nodea, size: 1 }); // Node A is its own root initially.
        /// assert_eq!(uf.find(nodeb).expect("Node should exist."), GroupRoot { ptr: nodeb, size: 1 }); // Node B is its own root initially.
        /// assert_eq!(uf.find(nodec).expect("Node should exist."), GroupRoot { ptr: nodec, size: 1 }); // Node C is its own root initially.
        ///
        /// uf.union(noded, nodee).unwrap();
        /// uf.union(nodeg, nodef).unwrap();
        ///
        /// assert_eq!(uf.find(noded).expect("Node should exist."), GroupRoot { ptr: noded, size: 2 }); // Node D is the root of {D, E}.
        /// assert_eq!(uf.find(nodee).expect("Node should exist."), GroupRoot { ptr: noded, size: 2 }); // Node E is in the group {D, E}.
        ///
        /// assert_eq!(uf.find(nodeg).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 2 }); // Node G is the root of {G, F}.
        /// assert_eq!(uf.find(nodef).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 2 }); // Node F is in the group {G, F}.
        ///
        /// uf.union(nodea, nodef).unwrap();
        /// assert_eq!(uf.find(nodea).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 3 }); // Group A added is now in the group F: {A, G, F}.
        ///
        /// uf.union(nodeb, nodec).unwrap();
        /// assert_eq!(uf.find(nodeb).expect("Node should exist."), GroupRoot { ptr: nodeb, size: 2 }); // Group C added is now added to group B:  {B, C}.
        ///
        /// uf.union(nodea, nodec).unwrap();
        /// assert_eq!(uf.find(nodea).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 5 }); // Group B is now added to group F:  {A, B, C, G, F}.
        ///
        /// assert_eq!(uf.union(nodea, nodeb), Err(UnionFindError::NodesInSameGroup)); // Nodes are already in the same group.
        ///
        /// uf.union(nodea, nodee).unwrap();
        /// assert_eq!(uf.find(nodee).expect("Node should exist."), GroupRoot { ptr: nodeg, size: 7 }); // Group D is now added to group F:  {A, B, C, D, E, G, F}.
        /// 
        /// assert_eq!(uf.count_groups(), 1); // There is only one group in the UnionFind structure.
        /// ```
        pub fn union(
            &mut self,
            node_a: StaticNodePtr,
            node_b: StaticNodePtr,
        ) -> Result<(), UnionFindError> {
            let root_a = self.find(node_a);
            let root_b = self.find(node_b);

            if let (Some(root_a), Some(root_b)) = (root_a, root_b) {
                if root_a == root_b {
                    return Err(UnionFindError::NodesInSameGroup);
                }

                // Union by size: Attach the smaller tree under the larger tree
                if root_a.size < root_b.size {
                    self.parent[*root_a.ptr] = root_b.ptr;
                    self.group_size[*root_b.ptr] += self.group_size[*root_a.ptr];
                } else {
                    self.parent[*root_b.ptr] = root_a.ptr;
                    self.group_size[*root_a.ptr] += self.group_size[*root_b.ptr];
                }
                Ok(())
            } else {
                Err(UnionFindError::NodesNotFromSameGraph)
            }
        }

        pub fn count_groups(&self) -> usize {
            self.parent
                .iter()
                .enumerate()
                .filter(|(idx, &p)| *idx == *p)
                .count()
        }

        fn partition_into_groups(&self) -> Vec<(GroupRoot, Vec<StaticNodePtr>)> {
            let mut groups = HashMap::new();

            for (idx, &parent) in self.parent.iter().enumerate() {
                if parent.idx == idx {
                    // If the node is a root
                    groups.entry(parent).or_insert_with(Vec::new).push(parent);
                } else {
                    let mut parent = parent;
                    // While the parent is not the root, keep traversing the path to the root.
                    while *parent != *self.parent[*parent] {
                        let next = self.parent[parent.idx];
                        parent = next;
                    }

                    groups
                        .entry(parent)
                        .or_insert_with(Vec::new)
                        .push(StaticNodePtr { idx });
                }
            }

            groups
                .into_iter()
                .map(|(root, kids)| {
                    (
                        GroupRoot {
                            ptr: root,
                            size: self.group_size[root.idx],
                        },
                        kids,
                    )
                })
                .collect()
        }
    }

    impl<'graph> Debug for UnionFind<'graph> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.debug_struct("UnionFind")
                .field(
                    "groups",
                    &self
                        .partition_into_groups()
                        .iter()
                        .map(|(root, kids)| {
                            let (root, kids) = (
                                *root.ptr,
                                kids.iter().map(|&ptr| ptr.idx).collect::<Vec<_>>(),
                            );
                            format!("Root: {:?} <== {:?}", root, kids)
                        })
                        .collect::<Vec<_>>(),
                )
                .finish()
        }
    }
}
