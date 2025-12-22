pub mod algorithms;

use std::collections::{HashMap, VecDeque};
use std::fmt::Formatter;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};

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
/// - Removing nodes or edges from the graph are not possible as this graph represents a static graph.
///
/// # Type Parameters
/// * `N` - The type of data stored in the nodes.
/// * `E` - The type of data stored in the edges.
///
/// # Examples
///
/// ## Create a new graph
/// ```
/// use aoc_utils_rust::graph::{StaticNodePtr, EdgeRelationship};
/// use aoc_utils_rust::graph::StaticGraph;
/// let mut graph = StaticGraph::new();
///
/// // Add nodes to the graph
/// let node_a_ptr: StaticNodePtr = graph.add_node("A");
/// let node_b_ptr: StaticNodePtr = graph.add_node("B");
/// let node_c_ptr: StaticNodePtr = graph.add_node("C");
///
/// let edge_data = ();
///
/// // Add edges between nodes
/// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(edge_data)).unwrap();
/// graph.add_edge(node_b_ptr, node_c_ptr, EdgeRelationship::AToB(edge_data)).unwrap();
/// graph.add_edge(node_c_ptr, node_a_ptr, EdgeRelationship::AToB(edge_data)).unwrap();
///
/// // Find a node by data
/// let node_a_data: &str = graph.get_node(node_a_ptr).unwrap();
/// assert_eq!(node_a_data, "A");
///
/// let node_b_data: &str = graph.get_node(node_b_ptr).unwrap();
/// assert_eq!(node_b_data, "B");
///
/// let node_c_data: &str = graph.get_node(node_c_ptr).unwrap();
/// assert_eq!(node_c_data, "C");
/// ```
///
/// ## Create a graph from a HashMap
/// ```
/// use std::collections::HashMap;
/// use aoc_utils_rust::graph::StaticGraph;
/// let mut map = HashMap::new();
/// map.insert("A", "B");
/// map.insert("B", "C");
/// let graph: StaticGraph<&str, ()> = StaticGraph::from(map);
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
/// use self::aoc_utils_rust::graph::{StaticGraph, EdgeRelationship};
/// let edges = [
///     ("A", "B", EdgeRelationship::AToB(2)),
///     ("B", "C", EdgeRelationship::BToA(10)),
///     ("C", "A", EdgeRelationship::BiDirectional{
///         a_to_b: 1,
///         b_to_a: 5,
///     }),
/// ];
/// let graph: StaticGraph<&str, u8> = StaticGraph::from(edges);
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
/// use self::aoc_utils_rust::graph::StaticNodePtr;
/// use self::aoc_utils_rust::graph::{StaticGraph, EdgeRelationship};
/// let edges = [
///     ("A", "B", EdgeRelationship::AToB(2)),
///     ("B", "C", EdgeRelationship::BToA(10)),
///     ("C", "A", EdgeRelationship::BiDirectional{
///         a_to_b: 1,
///         b_to_a: 5,
///     }),
/// ];
/// let graph: StaticGraph<&str, u8> = StaticGraph::from(edges);
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
/// let neighbours = graph.neighbours_iter(node_a).collect::<HashSet<(StaticNodePtr, &u8)>>();
/// assert_eq!(
///     neighbours,
///     vec![
///         (graph.find_node_index(|node| *node == "B").unwrap(), &2u8),
///         (graph.find_node_index(|node| *node == "C").unwrap(), &5),
///     ].into_iter().collect::<HashSet<_>>());
/// ```
///
#[derive(Default)]
pub struct StaticGraph<N, E> {
    nodes: Vec<StaticNode<N>>,
    edges: Vec<StaticEdge<E>>,
}

/// Represents the index of a node in the graph.
///
/// This struct is a transparent wrapper around a `usize` and is used to uniquely
/// identify nodes within the graph.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct StaticNodePtr {
    idx: usize,
}

/// A node in the graph.
///
/// # Type Parameters
///
/// * `N` - The type of data stored in the node.
#[derive(Debug)]
struct StaticNode<N> {
    /// The data stored in the node.
    data: N,

    /// The index of the node in the graph.
    node_index: StaticNodePtr,

    /// The index of the first edge connected to this node, if any.
    first_edge: Option<StaticEdgePtr>,
}

/// Represents the index of an edge in the graph.
///
/// Used to uniquely identify edges within the graph.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct StaticEdgePtr {
    /// The index of the edge in the graph.
    idx: usize,
}

/// An edge in the graph.
///
/// # Type Parameters
///
/// * `E` - The type of data stored in the edge.
#[derive(Debug)]
struct StaticEdge<E> {
    /// The data stored in the edge.
    data: E,

    /// The index of the destination node.
    to: StaticNodePtr,

    /// The index of the source node. This serves as the unique holder of the edge,
    /// representing the node that owns or originates the edge.
    /// The holder is important for efficiently traversing and managing edge connections in the graph.
    holder: StaticNodePtr,

    /// The index of the next edge connected to the same source node, if any.
    next_edge: Option<StaticEdgePtr>,
}

/// Core methods
impl<N, E> StaticGraph<N, E> {
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
    /// use aoc_utils_rust::graph::StaticGraph;
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
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
    /// use self::aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    /// let node_b_ptr: StaticNodePtr = graph.add_node("B");
    ///
    /// let found_node = graph.find_node_index(|node| *node == "A");
    /// assert_eq!(found_node, Some(node_a_ptr));
    ///
    /// let not_found_node = graph.find_node_index(|node| *node == "C");
    /// assert_eq!(not_found_node, None);
    /// ```
    pub fn find_node_index<F>(&self, find_fn: F) -> Option<StaticNodePtr>
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
    /// use self::aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    ///
    /// let node_a_data = graph.get_node(node_a_ptr).unwrap();
    /// assert_eq!(node_a_data, &"A");
    /// ```
    pub fn get_node(&self, node_index: StaticNodePtr) -> Option<&N> {
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
    /// use aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    ///
    /// let node_a_data = graph.get_node_mut(node_a_ptr).unwrap();
    /// *node_a_data = "B";
    ///
    /// let node_a_data = graph.get_node(node_a_ptr).unwrap();
    /// assert_eq!(node_a_data, &"B");
    /// ```
    pub fn get_node_mut(&mut self, node_index: StaticNodePtr) -> Option<&mut N> {
        self.nodes
            .get_mut(node_index.idx)
            .map(|node| &mut node.data)
    }

    pub fn get_edge(&self, edge_index: StaticEdgePtr) -> Option<&E> {
        self.edges.get(edge_index.idx).map(|edge| &edge.data)
    }

    /// Gets the edge connection of the edge at the specified index.
    ///
    ///
    pub fn get_edge_connection(
        &self,
        edge_index: StaticEdgePtr,
    ) -> Option<(StaticNodePtr, StaticNodePtr)> {
        self.edges
            .get(edge_index.idx)
            .map(|edge| (edge.holder, edge.to))
    }

    pub fn get_edge_mut(&mut self, edge_index: StaticEdgePtr) -> Option<&mut E> {
        self.edges
            .get_mut(edge_index.idx)
            .map(|edge| &mut edge.data)
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
    /// use self::aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    ///
    /// let node_a_data = graph.get_node(node_a_ptr).unwrap();
    /// assert_eq!(node_a_data, &"A");
    /// ```
    pub fn add_node(&mut self, data: N) -> StaticNodePtr {
        let node_index = StaticNodePtr {
            idx: self.nodes.len(),
        };
        self.nodes.push(StaticNode {
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
    /// use self::aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    /// let node_b_ptr: StaticNodePtr = graph.add_node("B");
    ///
    /// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let neighbours = graph.neighbours_iter(node_a_ptr).collect::<Vec<_>>();
    /// assert_eq!(neighbours.len(), 1);
    /// assert_eq!(neighbours[0].0, node_b_ptr);
    /// ```
    pub fn add_edge(
        &mut self,
        a_ptr: StaticNodePtr,
        b_ptr: StaticNodePtr,
        edge_relationship: EdgeRelationship<E>,
    ) -> Result<(), StaticNodePtr> {
        fn add_helper<N, E>(
            graph: &mut StaticGraph<N, E>,
            a_ptr: StaticNodePtr,
            b_ptr: StaticNodePtr,
            edge_data: E,
        ) -> Result<(), StaticNodePtr> {
            let new_edge_index = Some(StaticEdgePtr {
                idx: graph.edges.len(),
            });

            graph.edges.push(StaticEdge {
                data: edge_data,
                // Do a trial index to validate the b_ptr if it is valid. If it is not valid,
                // return an error telling the caller that the ptr that's invalid
                to: graph.get_node(b_ptr).ok_or(b_ptr).map(|_| b_ptr)?,
                holder: graph.get_node(a_ptr).ok_or(a_ptr).map(|_| a_ptr)?,
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
    /// use self::aoc_utils_rust::graph::{StaticGraph, EdgeRelationship};
    ///
    /// let mut graph = StaticGraph::<_, u8>::new();
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
    fn get_edge_node(&self, edge_index: StaticEdgePtr) -> Option<&StaticEdge<E>> {
        self.edges.get(edge_index.idx)
    }

    /// Calculates the in-degrees of all nodes in the graph.
    ///
    /// This function returns a vector of tuples where each tuple contains a `NodePtr` and the corresponding in-degree.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::graph::{StaticGraph, EdgeRelationship};
    ///
    /// let mut graph = StaticGraph::new();
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
    /// assert_eq!(in_degrees[0], (node_a, 0));
    /// assert_eq!(in_degrees[1], (node_b, 1));
    /// assert_eq!(in_degrees[2], (node_c, 2));
    /// assert_eq!(in_degrees[3], (node_d, 1));
    /// ```
    pub fn get_in_degrees(&self) -> Vec<(StaticNodePtr, u32)> {
        let mut in_degrees = vec![(StaticNodePtr { idx: 0 }, 0); self.nodes.len()];
        for (idx, node) in self.nodes.iter().enumerate() {
            in_degrees[node.node_index.idx].0 = StaticNodePtr { idx };
            for (neighbour, _) in self.neighbours_iter(node.node_index) {
                in_degrees[neighbour.idx].1 += 1;
            }
        }
        in_degrees
    }

    /// Counts the number of nodes reachable from the given node.
    ///
    /// This function performs a breadth-first search (BFS) to count all nodes
    /// that can be reached from the specified starting node.
    ///
    /// # Arguments
    ///
    /// * `static_node_ptr` - The starting node pointer.
    ///
    /// # Returns
    ///
    /// The number of nodes reachable from the starting node.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::graph::{EdgeRelationship , StaticGraph};
    ///
    /// let mut graph = StaticGraph::new();
    /// let node_a = graph.add_node("A");
    /// let node_b = graph.add_node("B");
    /// let node_c = graph.add_node("C");
    /// let node_d = graph.add_node("D");
    /// let node_e = graph.add_node("E");
    /// graph.add_edge(node_a, node_b, EdgeRelationship::AToB(())).unwrap();
    /// graph.add_edge(node_b, node_c, EdgeRelationship::BiDirectional {a_to_b : (), b_to_a: () }).unwrap();
    /// graph.add_edge(node_d, node_e, EdgeRelationship::BiDirectional {a_to_b : (), b_to_a: () }).unwrap();
    ///
    /// let ptrs = graph.get_nodes_reachable_from(node_a);
    /// assert_eq!(ptrs, vec![node_a, node_b, node_c].into_boxed_slice());
    /// assert_eq!(ptrs.len(), 3);
    ///
    /// let ptrs = graph.get_nodes_reachable_from(node_d);
    /// assert_eq!(ptrs, vec![node_d, node_e].into_boxed_slice());
    /// assert_eq!(ptrs.len(), 2);
    /// ```
    pub fn get_nodes_reachable_from(&self, static_node_ptr: StaticNodePtr) -> Box<[StaticNodePtr]> {
        let mut visited = vec![false; self.nodes.len()];
        let mut queue = VecDeque::new();

        queue.push_back(static_node_ptr);

        while let Some(curr_node) = queue.pop_front() {
            if visited[curr_node.idx] {
                continue;
            }
            visited[curr_node.idx] = true;

            for (neighbour, _) in self.neighbours_iter(curr_node) {
                if !visited[neighbour.idx] {
                    queue.push_back(neighbour);
                }
            }
        }

        visited
            .into_iter()
            .enumerate()
            .filter(|(_, visited)| *visited)
            .map(|(idx, _)| StaticNodePtr { idx })
            .collect::<Box<_>>()
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
    /// use self::aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    /// let node_b_ptr: StaticNodePtr = graph.add_node("B");
    /// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let neighbours = graph.neighbours_iter(node_a_ptr).collect::<Vec<_>>();
    /// assert_eq!(neighbours.len(), 1);
    /// assert_eq!(neighbours[0].0, node_b_ptr);
    /// ```
    pub fn neighbours_iter(&self, node_index: StaticNodePtr) -> Neighbours<'_, N, E> {
        Neighbours {
            graph: self,
            edges: self.nodes[node_index.idx].first_edge.clone(),
        }
    }
}

impl Deref for StaticNodePtr {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.idx
    }
}

impl Deref for StaticEdgePtr {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.idx
    }
}

impl DerefMut for StaticNodePtr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.idx
    }
}

impl DerefMut for StaticEdgePtr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.idx
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
/// use self::aoc_utils_rust::graph::{StaticGraph, StaticNodePtr};
///
/// let mut graph = StaticGraph::<_, ()>::new();
/// let node_a_ptr: StaticNodePtr = graph.add_node("A");
/// let node_b_ptr: StaticNodePtr = graph.add_node("B");
/// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
///
/// let neighbours = graph.neighbours_iter(node_a_ptr).collect::<Vec<_>>();
/// assert_eq!(neighbours.len(), 1);
/// assert_eq!(neighbours[0].0, node_b_ptr);
/// ```
pub struct Neighbours<'a, N, E> {
    graph: &'a StaticGraph<N, E>,
    edges: Option<StaticEdgePtr>,
}

impl<'a, N, E> Iterator for Neighbours<'a, N, E>
where
    E: 'a,
{
    type Item = (StaticNodePtr, &'a E);

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
    /// use aoc_utils_rust::graph::{StaticGraph, StaticNodePtr, EdgeRelationship};
    ///
    /// let mut graph = StaticGraph::<_, ()>::new();
    /// let node_a_ptr: StaticNodePtr = graph.add_node("A");
    /// let node_b_ptr: StaticNodePtr = graph.add_node("B");
    /// graph.add_edge(node_a_ptr, node_b_ptr, EdgeRelationship::AToB(())).unwrap();
    ///
    /// let mut neighbours_iter = graph.neighbours_iter(node_a_ptr);
    /// let first_neighbour = neighbours_iter.next().unwrap();
    /// assert_eq!(first_neighbour.0, node_b_ptr);
    /// assert!(neighbours_iter.next().is_none());
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.clone().map(|edge_index| {
            let edge = self.graph.get_edge_node(edge_index).unwrap();
            self.edges = edge.next_edge.clone();
            (edge.to, &edge.data)
        })
    }
}

impl<N, E> std::fmt::Debug for StaticGraph<N, E>
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

impl<E> Hash for EdgeRelationship<E>
where
    E: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            EdgeRelationship::BiDirectional { a_to_b, b_to_a } => {
                0.hash(state);
                a_to_b.hash(state);
                b_to_a.hash(state);
            }
            EdgeRelationship::AToB(data) => {
                1.hash(state);
                data.hash(state);
            }
            EdgeRelationship::BToA(data) => {
                2.hash(state);
                data.hash(state);
            }
        }
    }
}

impl<N, E> From<HashMap<N, N>> for StaticGraph<N, E>
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
        let mut graph = StaticGraph::with_capacity(hash_map.len());
        for (from, to) in hash_map {
            graph.add_edge_by_data(from, to, EdgeRelationship::AToB(E::default()));
        }
        graph
    }
}

impl<N, E> From<HashMap<N, Vec<N>>> for StaticGraph<N, E>
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
        let mut graph = StaticGraph::with_capacity(hash_map.len());
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

impl<N, E> From<Box<[(N, N, EdgeRelationship<E>)]>> for StaticGraph<N, E>
where
    N: PartialEq + Eq,
{
    /// Creates a graph from a boxed slice of tuples.
    fn from(slice: Box<[(N, N, EdgeRelationship<E>)]>) -> Self {
        let mut graph = StaticGraph::with_capacity(slice.len());

        for (from, to, relationship) in slice.into_vec().into_iter() {
            graph.add_edge_by_data(from, to, relationship);
        }

        graph
    }
}

impl<N, E, const S: usize> From<[(N, N, EdgeRelationship<E>); S]> for StaticGraph<N, E>
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
        let mut graph = StaticGraph::with_capacity(array_tuple.len());

        for (from, to, relationship) in array_tuple {
            graph.add_edge_by_data(from, to, relationship);
        }

        graph
    }
}
