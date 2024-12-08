use std::collections::HashMap;
use std::fmt::Formatter;

/// A graph data structure where nodes and edges are stored in vectors.
///
/// This implementation is inspired by the blog post ["Modeling graphs in Rust using vector indices"
/// by Niko Matsakis](https://smallcultfollowing.com/babysteps/blog/2015/04/06/modeling-graphs-in-rust-using-vector-indices/).
/// The high-level idea is to represent a "pointer" to a node or edge using an index. A graph consists
/// of a vector of nodes and a vector of edges, much like the mathematical description G=(V,E).
///
/// # Advantages
/// - This approach aligns well with Rust's ownership model.
/// - Unlike `Rc` pointers, an index alone is not enough to mutate the graph, which allows tracking
///   the mutability of the graph as a whole.
/// - Graphs implemented this way can easily be sent between threads and used in data-parallel code.
/// - The overall data structure is very compact, with no need for separate allocations for each node.
///
/// # Disadvantages
/// - Removing nodes or edges from the graph can be problematic, as it may lead to "dangling indices"
///   or require a placeholder, similar to issues with `malloc`/`free`. `(For now removal is not implemented.)`
/// - Indices from one graph should not be used with another graph to avoid misuse.
///
/// # Type Parameters
/// * `N` - The type of data stored in the nodes.
/// * `E` - The type of data stored in the edges.
///
/// # Examples
///
/// ## Create a new graph
/// ```
/// use aoc_utils_rust::graph::{NodePtr, EdgeRelationship};
/// use self::aoc_utils_rust::graph::Graph;
/// let mut graph = Graph::new();
///
/// // Add nodes to the graph
/// let node_a_ptr: NodePtr = graph.add_node("A");
/// let node_b_ptr: NodePtr = graph.add_node("B");
/// let node_c_ptr: NodePtr = graph.add_node("C");
///
/// let edge_data = ();
///
/// // Add edges between nodes
/// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(edge_data)).unwrap();
/// graph.add_edge(node_b_ptr, node_c_ptr, EdgeRelationship::AToB(edge_data)).unwrap();
/// graph.add_edge(node_c_ptr, node_a_ptr, EdgeRelationship::AToB(edge_data)).unwrap();
///
/// // Find a node by data
/// let node_a_data: &str = graph.get(node_a_ptr).unwrap();
/// assert_eq!(node_a_data, "A");
///
/// let node_b_data: &str = graph.get(node_b_ptr).unwrap();
/// assert_eq!(node_b_data, "B");
///
/// let node_c_data: &str = graph.get(node_c_ptr).unwrap();
/// assert_eq!(node_c_data, "C");
/// ```
///
/// ## Create a graph from a HashMap
/// ```
/// use std::collections::HashMap;
/// use self::aoc_utils_rust::graph::Graph;
/// let mut map = HashMap::new();
/// map.insert("A", "B");
/// map.insert("B", "C");
/// let graph: Graph<&str, ()> = Graph::from(map);
/// println!("{:?}", graph);
/// // Output:
/// // Graph: (3 nodes) {
/// //     Node: (NodePtr { idx: 0 }) (Data: "A") : [
/// //         Edge: '()' ->  To: "B"
/// //     ]
/// //     Node: (NodePtr { idx: 1 }) (Data: "B") : [
/// //         Edge: '()' ->  To: "C"
/// //     ]
/// //     Node: (NodePtr { idx: 2 }) (Data: "C") : [
/// //     ]
/// // }
///
/// ```
///
/// ## Create a graph from a vector of tuples with weighted edges
/// ```
/// use self::aoc_utils_rust::graph::{Graph, EdgeRelationship};
/// let edges = [
///     ("A", "B", EdgeRelationship::AToB(2)),
///     ("B", "C", EdgeRelationship::BToA(10)),
///     ("C", "A", EdgeRelationship::BiDirectional{
///         a_to_b: 1,
///         b_to_a: 5,
///     }),
/// ];
/// let graph: Graph<&str, u8> = Graph::from(edges);
/// // println!("{:?}", graph);
/// // Output:
/// // Graph: (3 nodes) {
/// //     Node: (NodePtr { idx: 0 }) (Data: "A") : [
/// //         Edge: 2 ->  To: "B"
/// //         Edge: 5 ->  To: "C"
/// //     ]
/// //     Node: (NodePtr { idx: 1 }) (Data: "B") : [
/// //     ]
/// //     Node: (NodePtr { idx: 2 }) (Data: "C") : [
/// //         Edge: 1 ->  To: "A"
/// //         Edge: 10 ->  To: "B"
/// //     ]
/// // }
/// ```
///
/// ## Iterate through the neighbors of a node
/// ```
/// use std::collections::HashSet;
/// use self::aoc_utils_rust::graph::NodePtr;
/// use self::aoc_utils_rust::graph::{Graph, EdgeRelationship};
/// let edges = [
///     ("A", "B", EdgeRelationship::AToB(2)),
///     ("B", "C", EdgeRelationship::BToA(10)),
///     ("C", "A", EdgeRelationship::BiDirectional{
///         a_to_b: 1,
///         b_to_a: 5,
///     }),
/// ];
/// let graph: Graph<&str, u8> = Graph::from(edges);
/// // println!("{:?}", graph);
/// // Output:
/// // Graph: (3 nodes) {
/// //     Node: (NodePtr { idx: 0 }) (Data: "A") : [
/// //         Edge: 2 ->  To: "B"
/// //         Edge: 5 ->  To: "C"
/// //     ]
/// //     Node: (NodePtr { idx: 1 }) (Data: "B") : [
/// //     ]
/// //     Node: (NodePtr { idx: 2 }) (Data: "C") : [
/// //         Edge: 1 ->  To: "A"
/// //         Edge: 10 ->  To: "B"
/// //     ]
/// // }
///
/// let node_a = graph.find_node_index(|node| *node == "A").unwrap();
/// // Iterate through the neighbors of node A collecting them into a vector
/// let neighbours = graph.neighbours_iter(node_a).collect::<Vec<(NodePtr, &u8)>>();
/// assert_eq!(
///     neighbours.into_iter().collect::<HashSet<_>>(),
///     vec![
///         (graph.find_node_index(|node| *node == "B").unwrap(), &2u8),
///         (graph.find_node_index(|node| *node == "C").unwrap(), &5),
///     ].into_iter().collect::<HashSet<_>>());
/// ```
///
#[derive(Default)]
pub struct Graph<N, E> {
    nodes: Vec<Node<N>>,
    edges: Vec<Edge<E>>,
}

/// Represents the index of a node in the graph.
///
/// This struct is a transparent wrapper around a `usize` and is used to uniquely
/// identify nodes within the graph.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NodePtr {
    idx: usize,
}

/// A node in the graph.
///
/// # Type Parameters
///
/// * `N` - The type of data stored in the node.
#[derive(Debug)]
struct Node<N> {
    /// The data stored in the node.
    data: N,

    /// The index of the node in the graph.
    node_index: NodePtr,

    /// The index of the first edge connected to this node, if any.
    first_edge: Option<EdgePtr>,
}

/// Represents the index of an edge in the graph.
///
/// Used to uniquely identify edges within the graph.
#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EdgePtr {
    /// The index of the edge in the graph.
    idx: usize,
}

/// An edge in the graph.
///
/// # Type Parameters
///
/// * `E` - The type of data stored in the edge.
#[derive(Debug)]
struct Edge<E> {
    /// The data stored in the edge.
    data: E,

    /// The index of the destination node.
    to: NodePtr,

    /// The index of the next edge connected to the same source node, if any.
    next_edge: Option<EdgePtr>,
}

/// Core methods
impl<N, E> Graph<N, E> {
    /// Creates a new, empty graph.
    ///
    /// # Returns
    ///
    /// A new instance of `Graph`.
    #[inline]
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }

    /// Creates a new graph with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the graph's nodes and edges vectors.
    ///
    /// # Returns
    ///
    /// A new instance of `Graph` with the specified capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(capacity),
            edges: Vec::with_capacity(capacity),
        }
    }

    /// Clears all nodes and edges from the graph.
    ///
    /// This method removes all nodes and edges, effectively resetting the graph to an empty state.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::graph::Graph;
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// graph.add_node("A");
    /// graph.add_node("B");
    /// graph.clear();
    ///
    /// assert_eq!(graph.len(), 0);
    /// assert!(graph.nodes().is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.edges.clear();
    }

    /// Returns a vector of references to the data stored in the nodes.
    ///
    /// # Returns
    ///
    /// A `Vec` containing references to the data of each node in the graph.
    pub fn nodes(&self) -> Vec<&N> {
        self.nodes.iter().map(|node| &node.data).collect::<Vec<_>>()
    }

    /// Finds the index of a node that satisfies the given predicate.
    ///
    /// # Arguments
    ///
    /// * `find_fn` - A closure that takes a reference to a node's data and returns `true` if the node
    ///   matches the criteria, or `false` otherwise.
    ///
    /// # Returns
    ///
    /// An `Option` containing the `NodePtr` of the first node that matches the predicate, or `None` if no
    /// nodes match.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the closure used to find the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    /// let node_b_ptr: NodePtr = graph.add_node("B");
    ///
    /// let found_node = graph.find_node_index(|node| *node == "A");
    /// assert_eq!(found_node, Some(node_a_ptr));
    ///
    /// let not_found_node = graph.find_node_index(|node| *node == "C");
    /// assert_eq!(not_found_node, None);
    /// ```
    pub fn find_node_index<F>(&self, find_fn: F) -> Option<NodePtr>
    where
        N: PartialEq + Eq,
        F: Fn(&N) -> bool,
    {
        self.nodes
            .iter()
            .find(|node| find_fn(&node.data))
            .map(|node| node.node_index)
    }

    /// # Returns
    ///
    /// Gets the number of nodes in the graph.
    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Gets a reference to the data stored in the node at the specified index.
    ///
    /// # Arguments
    ///
    /// * `node_index` - The index of the node.
    ///
    /// # Returns
    ///
    /// A reference to the data stored in the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    ///
    /// let node_a_data = graph.get(node_a_ptr).unwrap();
    /// assert_eq!(node_a_data, &"A");
    /// ```
    pub fn get(&self, node_index: NodePtr) -> Option<&N> {
        self.nodes.get(node_index.idx).map(|node| &node.data)
    }

    /// Gets a mutable reference to the data stored in the node at the specified index.
    ///
    /// # Arguments
    ///
    /// * `node_index` - The index of the node.
    ///
    /// # Returns
    ///
    /// A mutable reference to the data stored in the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    ///
    /// let node_a_data = graph.get_mut(node_a_ptr).unwrap();
    /// *node_a_data = "B";
    ///
    /// let node_a_data = graph.get(node_a_ptr).unwrap();
    /// assert_eq!(node_a_data, &"B");
    /// ```
    pub fn get_mut(&mut self, node_index: NodePtr) -> Option<&mut N> {
        self.nodes
            .get_mut(node_index.idx)
            .map(|node| &mut node.data)
    }

    /// Adds a new node with the specified data to the graph.
    ///
    /// # Arguments
    ///
    /// * `data` - The data to store in the new node.
    ///
    /// # Returns
    ///
    /// The `NodeIndex` of the newly added node.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    ///
    /// let node_a_data = graph.get(node_a_ptr).unwrap();
    /// assert_eq!(node_a_data, &"A");
    /// ```
    pub fn add_node(&mut self, data: N) -> NodePtr {
        let node_index = NodePtr {
            idx: self.nodes.len(),
        };
        self.nodes.push(Node {
            data,
            node_index,
            first_edge: None,
        });

        node_index
    }

    /// Adds a new edge between two nodes in the graph.
    ///
    /// # Arguments
    ///
    /// * `a_ptr` - The index of a node.
    /// * `b_ptr` - The index of b node.
    /// * `edge_relationship` - The Relationship between `a_ptr` and `b_ptr`.
    ///
    /// # Returns
    /// A `Result` indicating success if nodes were connected successfully or and error denoting which pointer  .
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::graph::EdgeRelationship;
    /// use self::aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    /// let node_b_ptr: NodePtr = graph.add_node("B");
    ///
    /// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let neighbours = graph.neighbours_iter(node_a_ptr).collect::<Vec<_>>();
    /// assert_eq!(neighbours.len(), 1);
    /// assert_eq!(neighbours[0].0, node_b_ptr);
    /// ```
    pub fn add_edge(
        &mut self,
        a_ptr: NodePtr,
        b_ptr: NodePtr,
        edge_relationship: EdgeRelationship<E>,
    ) -> Result<(), NodePtr> {
        fn add_helper<N, E>(
            graph: &mut Graph<N, E>,
            a_ptr: NodePtr,
            b_ptr: NodePtr,
            edge_data: E,
        ) -> Result<(), NodePtr> {
            let new_edge_index = Some(EdgePtr {
                idx: graph.edges.len(),
            });

            graph.edges.push(Edge {
                data: edge_data,
                // Do a trial index to validate the b_ptr
                to: graph.get(b_ptr).ok_or(b_ptr).map(|_| b_ptr)?,
                next_edge: graph
                    .nodes
                    .get(a_ptr.idx)
                    .ok_or(a_ptr)
                    .map(|node| node.first_edge.clone())?,
            });

            graph.nodes[a_ptr.idx].first_edge = new_edge_index;

            Ok(())
        }

        match edge_relationship {
            EdgeRelationship::BiDirectional { a_to_b, b_to_a } => {
                add_helper(self, a_ptr, b_ptr, a_to_b)?;
                add_helper(self, b_ptr, a_ptr, b_to_a)
            }
            EdgeRelationship::AToB(edge) => add_helper(self, a_ptr, b_ptr, edge),
            EdgeRelationship::BToA(edge) => add_helper(self, b_ptr, a_ptr, edge),
        }
    }

    /// Adds a new edge between two nodes, identified by their data.
    ///
    /// # Arguments
    ///
    /// * `from` - The data of the source node.
    /// * `to` - The data of the destination node.
    /// * `edge_data` - The data to store in the new edge.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::graph::{Graph, EdgeRelationship};
    ///
    /// let mut graph = Graph::<_, u8>::new();
    /// graph.add_edge_by_data("A", "B", EdgeRelationship::AToB(2));
    /// graph.add_edge_by_data("B", "C", EdgeRelationship::BToA(10));
    /// graph.add_edge_by_data("C", "A", EdgeRelationship::BiDirectional { a_to_b: 1, b_to_a: 5 });
    ///
    /// let node_a = graph.find_node_index(|node| *node == "A").unwrap();
    /// let node_b = graph.find_node_index(|node| *node == "B").unwrap();
    /// let node_c = graph.find_node_index(|node| *node == "C").unwrap();
    ///
    /// let neighbours_a = graph.neighbours_iter(node_a).collect::<Vec<_>>();
    /// assert_eq!(neighbours_a.len(), 2);
    /// assert!(neighbours_a.contains(&(node_b, &2)));
    /// assert!(neighbours_a.contains(&(node_c, &5)));
    ///
    /// let neighbours_b = graph.neighbours_iter(node_b).collect::<Vec<_>>();
    /// assert_eq!(neighbours_b.len(), 0);
    ///
    /// let neighbours_c = graph.neighbours_iter(node_c).collect::<Vec<_>>();
    /// assert_eq!(neighbours_c.len(), 2);
    /// assert!(neighbours_c.contains(&(node_a, &1)));
    /// assert!(neighbours_c.contains(&(node_b, &10)));
    /// ```
    pub fn add_edge_by_data(&mut self, node_a: N, node_b: N, relationship: EdgeRelationship<E>)
    where
        N: PartialEq + Eq,
    {
        let a_index = self
            .find_node_index(|node| node == &node_a)
            .unwrap_or_else(|| self.add_node(node_a));

        let b_index = self
            .find_node_index(|node| node == &node_b)
            .unwrap_or_else(|| self.add_node(node_b));

        self.add_edge(a_index, b_index, relationship).expect("Should not fail to add edge as the nodes were newly added and therefore their NodePtrs are valid.");
    }

    /// Retrieves a reference to the edge at the specified index.
    ///
    /// # Arguments
    ///
    /// * `edge_index` - The index of the edge to retrieve.
    ///
    /// # Returns
    ///
    /// An `Option` containing a reference to the edge if it exists, or `None` if the index is out of bounds.
    fn get_edge(&self, edge_index: EdgePtr) -> Option<&Edge<E>> {
        self.edges.get(edge_index.idx)
    }

    /// Calculates the in-degrees of all nodes in the graph.
    ///
    /// This function returns a vector of tuples where each tuple contains a `NodePtr` and the corresponding in-degree.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use aoc_utils_rust::graph::{Graph, EdgeRelationship};
    ///
    /// let mut graph = Graph::new();
    /// let node_a = graph.add_node("A");
    /// let node_b = graph.add_node("B");
    /// let node_c = graph.add_node("C");
    /// let node_d = graph.add_node("D");
    ///
    /// graph.add_edge(node_a, node_b, EdgeRelationship::AToB(())).unwrap();
    /// graph.add_edge(node_a, node_c, EdgeRelationship::AToB(())).unwrap();
    /// graph.add_edge(node_b, node_c, EdgeRelationship::AToB(())).unwrap();
    /// graph.add_edge(node_c, node_d, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let in_degrees = graph.get_in_degrees();
    /// assert_eq!(in_degrees.len(), 4);
    /// assert_eq!(in_degrees[0], (node_a, None));
    /// assert_eq!(in_degrees[1], (node_b, Some(1)));
    /// assert_eq!(in_degrees[2], (node_c, Some(2)));
    /// assert_eq!(in_degrees[3], (node_d, Some(1)));
    /// ```
    fn get_in_degrees(&self) -> Vec<(NodePtr, Option<u32>)> {
        let mut in_degrees = vec![(NodePtr { idx: 0 }, None); self.nodes.len()];
        // FIXME: If removal is ever implemented, this will need to be updated to handle the removal of nodes.
        for (idx, node) in self.nodes.iter().enumerate() {
            in_degrees[node.node_index.idx].0 = NodePtr { idx };
            for (neighbour, _) in self.neighbours_iter(node.node_index) {
                *in_degrees[neighbour.idx].1.get_or_insert(0) += 1;
            }
        }
        in_degrees
    }

    /// Returns an iterator over the neighbors of the specified node.
    ///
    /// # Arguments
    ///
    /// * `node_index` - The index of the node whose neighbors are to be iterated.
    ///
    /// # Returns
    ///
    /// An iterator over the neighbors of the specified node. Each item in the iterator is a tuple
    /// containing the `NodePtr` of the neighbor and a reference to the edge data.
    ///
    /// # Panics
    ///
    /// This function will panic if the `node_index` is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::graph::EdgeRelationship;
    /// use self::aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    /// let node_b_ptr: NodePtr = graph.add_node("B");
    /// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let neighbours = graph.neighbours_iter(node_a_ptr).collect::<Vec<_>>();
    /// assert_eq!(neighbours.len(), 1);
    /// assert_eq!(neighbours[0].0, node_b_ptr);
    /// ```
    pub fn neighbours_iter(&self, node_index: NodePtr) -> Neighbours<N, E> {
        Neighbours {
            graph: self,
            edges: self.nodes[node_index.idx].first_edge.clone(),
        }
    }
}

/// Algorithms
impl<N, E> Graph<N, E> {
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
    ///  use aoc_utils_rust::graph::{Graph, NodePtr};
    ///
    ///  let mut input = HashMap::<i32, Vec<i32>>::new();
    ///  input.insert(1, vec![2, 3]);
    ///  input.insert(2, vec![3]);
    ///  input.insert(3, vec![4]);
    ///  input.insert(4, vec![]);
    ///
    ///  let mut graph = Graph::<_, ()>::from(input);
    ///
    ///  let topologically_sorted = graph
    ///         .topological_sort()
    ///         .expect("This graph does not contain cycles and is therefore topologically sortable.")
    ///         .iter()
    ///         .map(|node: &NodePtr| *graph.get(*node).expect("Node should exist as it was returned by topological_sort."))
    ///         .collect::<Vec<i32>>();
    ///
    ///  assert_eq!(topologically_sorted, vec![1, 2, 3, 4]);
    /// ```
    ///
    /// ### With cycles
    /// ```
    /// use aoc_utils_rust::graph::{Graph, NodePtr, EdgeRelationship};
    ///
    /// let mut graph = Graph::new();
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
    pub fn topological_sort(&self) -> Result<Vec<NodePtr>, ()> {
        let mut result = Vec::with_capacity(self.nodes.len());
        let mut zero_in_degree_nodes = Vec::new();

        let mut in_degrees = self.get_in_degrees();

        // Collect nodes with zero in-degree
        for (node_ptr, in_degree) in in_degrees.iter() {
            if *in_degree == None {
                zero_in_degree_nodes.push(*node_ptr);
            }
        }

        // Process nodes with zero in-degree
        while let Some(node) = zero_in_degree_nodes.pop() {
            result.push(node);

            for (neighbour, _) in self.neighbours_iter(node) {
                in_degrees[neighbour.idx].1.as_mut().map(|degree| {
                    *degree -= 1;
                    if *degree == 0 {
                        zero_in_degree_nodes.push(neighbour);
                    }
                });
            }
        }

        // Check if all nodes are processed
        if result.len() == in_degrees.len() {
            Ok(result)
        } else {
            Err(()) // Cycle detected
        }
    }
}

/// An iterator over the neighbors of a node in the graph.
///
/// # Type Parameters
///
/// * `N` - The type of data stored in the nodes.
/// * `E` - The type of data stored in the edges.
///
/// # Examples
///
/// ```
/// use aoc_utils_rust::graph::EdgeRelationship;
/// use self::aoc_utils_rust::graph::{Graph, NodePtr};
///
/// let mut graph = Graph::<_, ()>::new();
/// let node_a_ptr: NodePtr = graph.add_node("A");
/// let node_b_ptr: NodePtr = graph.add_node("B");
/// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
///
/// let neighbours = graph.neighbours_iter(node_a_ptr).collect::<Vec<_>>();
/// assert_eq!(neighbours.len(), 1);
/// assert_eq!(neighbours[0].0, node_b_ptr);
/// ```
pub struct Neighbours<'a, N, E> {
    graph: &'a Graph<N, E>,
    edges: Option<EdgePtr>,
}

impl<'a, N, E> Iterator for Neighbours<'a, N, E>
where
    E: 'a,
{
    type Item = (NodePtr, &'a E);

    /// Advances the iterator and returns the next neighbor of the node.
    ///
    /// # Returns
    ///
    /// An `Option` containing a tuple with the `NodePtr` of the neighbor and a reference to the edge data,
    /// or `None` if there are no more neighbors.
    ///
    /// # Panics
    ///
    /// This function will panic if the edge index is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::graph::{Graph, NodePtr, EdgeRelationship};
    ///
    /// let mut graph = Graph::<_, ()>::new();
    /// let node_a_ptr: NodePtr = graph.add_node("A");
    /// let node_b_ptr: NodePtr = graph.add_node("B");
    /// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let mut neighbours_iter = graph.neighbours_iter(node_a_ptr);
    /// let first_neighbour = neighbours_iter.next().unwrap();
    /// assert_eq!(first_neighbour.0, node_b_ptr);
    /// assert!(neighbours_iter.next().is_none());
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.clone().map(|edge_index| {
            let edge = self.graph.get_edge(edge_index).unwrap();
            self.edges = edge.next_edge.clone();
            (edge.to, &edge.data)
        })
    }
}

impl<N, E> std::fmt::Debug for Graph<N, E>
where
    N: std::fmt::Debug,
    E: std::fmt::Debug,
{
    /// Formats the graph using the given formatter.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter to use.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or failure.
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut visited = Vec::with_capacity(self.nodes.len());
        writeln!(f, "Graph: ({} nodes) {{", self.nodes.len())?;
        for nodes in self.nodes.iter() {
            if !visited.contains(&nodes.node_index) {
                let mut curr_edge = nodes.first_edge.clone();
                if curr_edge.is_none() {
                    writeln!(
                        f,
                        "\tNode: ({:?}) (Data: '{:?}') : []",
                        nodes.node_index, nodes.data
                    )?;
                    continue;
                }
                writeln!(
                    f,
                    "\tNode: ({:?}) (Data: '{:?}') : [",
                    nodes.node_index, nodes.data
                )?;
                while let Some(edge_index) = curr_edge.clone() {
                    let edge = &self.edges[edge_index.idx];
                    writeln!(
                        f,
                        "\t\tEdge: '{:?}' ->  Node: ({:?}) (Data: '{:?}')",
                        edge.data, edge.to, self.nodes[edge.to.idx].data
                    )?;
                    curr_edge = edge.next_edge.clone();
                }
                writeln!(f, "\t]")?;
                visited.push(nodes.node_index)
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

/// Defines the type of relationship between two nodes in the graph.
///
/// # Type Parameters
/// * `E` - The type of data stored in the edges.
#[derive(Debug, Clone)]
pub enum EdgeRelationship<E> {
    /// A bidirectional relationship between two nodes.
    /// Contains data for both directions (a->b and b->a).
    BiDirectional { a_to_b: E, b_to_a: E },

    /// A unidirectional relationship from node A to node B.
    AToB(E),

    /// A unidirectional relationship from node B to node A.
    BToA(E),
}

impl<N, E> From<HashMap<N, N>> for Graph<N, E>
where
    N: PartialEq + Eq,
    E: Default,
{
    /// Creates a graph from a `HashMap` where keys and values represent nodes.
    ///
    /// # Note
    /// Relationships are always from key to value.
    ///
    /// # Arguments
    ///
    /// * `hash_map` - The `HashMap` to convert into a graph.
    ///
    /// # Returns
    ///
    /// A new instance of `Graph`.
    fn from(hash_map: HashMap<N, N>) -> Self {
        let mut graph = Graph::with_capacity(hash_map.len());
        for (from, to) in hash_map {
            graph.add_edge_by_data(from, to, EdgeRelationship::AToB(E::default()));
        }
        graph
    }
}

impl<N, E> From<HashMap<N, Vec<N>>> for Graph<N, E>
where
    N: PartialEq + Eq,
    E: Default,
{
    /// Creates a graph from a `HashMap` where keys and values represent nodes.
    ///
    /// # Note
    /// Relationships are always from key to value.
    ///
    /// # Arguments
    ///
    /// * `hash_map` - The `HashMap` to convert into a graph.
    ///
    /// # Returns
    ///
    /// A new instance of `Graph`.
    fn from(hash_map: HashMap<N, Vec<N>>) -> Self {
        let mut graph = Graph::with_capacity(hash_map.len());
        for (from, to_many) in hash_map {
            let from = graph
                .find_node_index(|e| *e == from)
                .unwrap_or_else(|| graph.add_node(from));

            for to in to_many {
                let to = graph
                    .find_node_index(|e| *e == to)
                    .unwrap_or_else(|| graph.add_node(to));
                graph
                    .add_edge(from, to, EdgeRelationship::AToB(E::default()))
                    .unwrap();
            }
        }
        graph
    }
}

impl<N, E> From<Box<[(N, N, EdgeRelationship<E>)]>> for Graph<N, E>
where
    N: PartialEq + Eq,
{
    /// Creates a graph from a boxed slice of tuples.
    fn from(slice: Box<[(N, N, EdgeRelationship<E>)]>) -> Self {
        let mut graph = Graph::with_capacity(slice.len());

        for (from, to, relationship) in slice.into_vec().into_iter() {
            graph.add_edge_by_data(from, to, relationship);
        }

        graph
    }
}

impl<N, E, const S: usize> From<[(N, N, EdgeRelationship<E>); S]> for Graph<N, E>
where
    N: PartialEq + Eq,
{
    /// Creates a graph from a vector of tuples where each tuple represents an edge.
    ///
    /// # Arguments
    ///
    /// * `vec_tuple` - The vector of tuples to convert into a graph.
    ///
    /// # Returns
    ///
    /// A new instance of `Graph`.
    fn from(array_tuple: [(N, N, EdgeRelationship<E>); S]) -> Self {
        let mut graph = Graph::with_capacity(array_tuple.len());

        for (from, to, relationship) in array_tuple {
            graph.add_edge_by_data(from, to, relationship);
        }

        graph
    }
}
