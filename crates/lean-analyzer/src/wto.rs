//! src/wto.rs
//! Bourdoncle Weak Topological Ordering (WTO) and Bounded Trace Partitioning
//! for Lean 4 abstract interpretation.
//!
//! Literature anchors:
//! - Bourdoncle (1993), "Efficient chaotic iteration strategies with widenings", FMPA.
//! - Rival & Yi (2020), *Introduction to Static Analysis*, Ch. 5 (`RIVALYI s5.1 p1`).
//! - Arceri et al. (2023), *Challenges of Software Verification*, Ch. 1 (`ARCERI2023 s1.3 p1`).
//! - Rival & Mauborgne (2007), "The trace partitioning abstract domain", ACM TOPLAS.
//!
//! 

use crate::lattice::AbstractState;
use std::collections::BTreeMap;

/// An element of a Bourdoncle Weak Topological Ordering (WTO) over vertex IDs `0..N`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WtoElement {
    /// A single non-header vertex in the control-flow / call dependency graph.
    Vertex(usize),
    /// A strongly connected component with loop `head` and recursive sub-elements `body`.
    /// Stabilization proceeds recursively over `body`, applying widening at `head`.
    Component {
        head: usize,
        body: Vec<WtoElement>,
    },
}

/// Hierarchical Bourdoncle Weak Topological Ordering (WTO) of a directed graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WtoOrdering {
    pub elements: Vec<WtoElement>,
    pub num_vertices: usize,
}

struct TarjanBourdoncle<'a> {
    adj: &'a [Vec<usize>],
    dfn: Vec<usize>,
    stack: Vec<usize>,
    in_stack: Vec<bool>,
    num: usize,
}

impl<'a> TarjanBourdoncle<'a> {
    fn new(adj: &'a [Vec<usize>]) -> Self {
        let n = adj.len();
        Self {
            adj,
            dfn: vec![0; n],
            stack: Vec::with_capacity(n),
            in_stack: vec![false; n],
            num: 0,
        }
    }

    /// Bourdoncle's recursive Tarjan visit (`VISIT(v, partition)` from Fig. 4 of Bourdoncle 1993).
    fn visit(&mut self, v: usize, partition: &mut Vec<WtoElement>) -> usize {
        self.num += 1;
        self.dfn[v] = self.num;
        let mut head = self.dfn[v];
        let mut loop_detected = false;

        self.stack.push(v);
        self.in_stack[v] = true;

        for &succ in &self.adj[v] {
            if succ >= self.adj.len() {
                continue;
            }
            let min = if self.dfn[succ] == 0 {
                self.visit(succ, partition)
            } else {
                self.dfn[succ]
            };
            if min <= head && self.in_stack[succ] {
                head = min;
                loop_detected = true;
            }
        }

        if head == self.dfn[v] {
            // Pop component vertices down to `v`
            self.dfn[v] = usize::MAX;
            let mut element = self.stack.pop().unwrap_or(v);
            self.in_stack[element] = false;

            if loop_detected {
                let mut component_vertices = Vec::new();
                while element != v {
                    self.dfn[element] = 0;
                    component_vertices.push(element);
                    element = self.stack.pop().unwrap_or(v);
                    self.in_stack[element] = false;
                }
                let body = self.component(v);
                partition.push(WtoElement::Component { head: v, body });
            } else {
                partition.push(WtoElement::Vertex(v));
            }
        }

        head
    }

    /// Bourdoncle's `COMPONENT(v)` sub-partition builder after removing back-edges to `v`.
    fn component(&mut self, v: usize) -> Vec<WtoElement> {
        let mut sub_partition = Vec::new();
        for &succ in &self.adj[v] {
            if succ < self.adj.len() && self.dfn[succ] == 0 {
                self.visit(succ, &mut sub_partition);
            }
        }
        sub_partition.reverse();
        sub_partition
    }
}

impl WtoOrdering {
    /// Computes the Bourdoncle Weak Topological Ordering of a directed graph `adj`
    /// starting from `entry` (plus any remaining unvisited vertices in index order).
    pub fn from_adjacency(adj: &[Vec<usize>], entry: usize) -> Self {
        let n = adj.len();
        if n == 0 {
            return Self {
                elements: Vec::new(),
                num_vertices: 0,
            };
        }
        let mut builder = TarjanBourdoncle::new(adj);
        let mut partition = Vec::new();
        if entry < n && builder.dfn[entry] == 0 {
            builder.visit(entry, &mut partition);
        }
        for v in 0..n {
            if builder.dfn[v] == 0 {
                builder.visit(v, &mut partition);
            }
        }
        partition.reverse();
        Self {
            elements: partition,
            num_vertices: n,
        }
    }

    /// Executes Bourdoncle's recursive chaotic iteration strategy (`wto_fixpoint`) over
    /// `AbstractState` vectors, applying threshold widening at component heads (`head`)
    /// and narrowing once each component stabilizes.
    pub fn solve_fixpoint<F>(
        &self,
        init_states: &[AbstractState],
        mut transfer_vertex: F,
        thresholds: &[i64],
        widen_delay: usize,
        max_component_iters: usize,
    ) -> Vec<AbstractState>
    where
        F: FnMut(usize, &[AbstractState]) -> AbstractState,
    {
        let mut states: Vec<AbstractState> = (0..self.num_vertices)
            .map(|i| {
                init_states
                    .get(i)
                    .copied()
                    .unwrap_or_else(AbstractState::bottom)
            })
            .collect();

        Self::eval_sequence(
            &self.elements,
            &mut states,
            &mut transfer_vertex,
            thresholds,
            widen_delay,
            max_component_iters,
        );
        states
    }

    fn eval_sequence<F>(
        elements: &[WtoElement],
        states: &mut [AbstractState],
        transfer_vertex: &mut F,
        thresholds: &[i64],
        widen_delay: usize,
        max_component_iters: usize,
    ) where
        F: FnMut(usize, &[AbstractState]) -> AbstractState,
    {
        for elem in elements {
            match elem {
                WtoElement::Vertex(v) => {
                    if *v < states.len() {
                        let next = transfer_vertex(*v, states).refine_nat();
                        states[*v] = states[*v].join(&next).refine_nat();
                    }
                }
                WtoElement::Component { head, body } => {
                    Self::stabilize_component(
                        *head,
                        body,
                        states,
                        transfer_vertex,
                        thresholds,
                        widen_delay,
                        max_component_iters,
                    );
                }
            }
        }
    }

    fn stabilize_component<F>(
        head: usize,
        body: &[WtoElement],
        states: &mut [AbstractState],
        transfer_vertex: &mut F,
        thresholds: &[i64],
        widen_delay: usize,
        max_component_iters: usize,
    ) where
        F: FnMut(usize, &[AbstractState]) -> AbstractState,
    {
        if head >= states.len() {
            return;
        }
        // Ascending phase with threshold widening at `head`
        for iter in 0..max_component_iters {
            let prev_head = states[head];
            let raw_next = transfer_vertex(head, states).refine_nat();
            let joined = prev_head.join(&raw_next).refine_nat();

            let next_head = if iter >= widen_delay {
                if thresholds.is_empty() {
                    prev_head.widen(&joined).refine_nat()
                } else {
                    prev_head.widen_with_thresholds(&joined, thresholds).refine_nat()
                }
            } else {
                joined
            };

            states[head] = next_head;

            // Stabilize inner body under updated head
            Self::eval_sequence(
                body,
                states,
                transfer_vertex,
                thresholds,
                widen_delay,
                max_component_iters,
            );

            // Check if component head has stabilized after inner body evaluation
            let post_head = transfer_vertex(head, states).refine_nat();
            if post_head.is_le(&states[head]) && states[head] == prev_head {
                break;
            }
        }

        // Descending (narrowing) pass at `head` followed by one body propagation pass
        let refined = transfer_vertex(head, states).refine_nat();
        states[head] = states[head].narrow(&refined).refine_nat();
        Self::eval_sequence(
            body,
            states,
            transfer_vertex,
            thresholds,
            widen_delay,
            1,
        );
    }
}

/// Bounded control-flow trace token (`match` / `ite` arm history) for Trace Partitioning
/// (`Rival & Mauborgne 2007`, `RIVALYI s5.3 p1`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TraceToken {
    /// Bounded FIFO sequence of branch labels (e.g., `true`, `false`, `0`, `succ`), capped at `max_depth`.
    pub history: Vec<u8>,
}

impl TraceToken {
    pub fn root() -> Self {
        Self {
            history: Vec::new(),
        }
    }

    pub fn push_branch(&self, branch_id: u8, max_depth: usize) -> Self {
        if max_depth == 0 {
            return Self::root();
        }
        let mut h = self.history.clone();
        if h.len() >= max_depth {
            h.remove(0);
        }
        h.push(branch_id);
        Self { history: h }
    }
}

/// Bounded Trace-Partitioned Abstract Domain mapping `TraceToken -> AbstractState`.
/// Keeps control-flow paths separated up to `max_depth` branch decisions before folding
/// older prefixes via lattice `join`, preserving path sensitivity without exponential blowup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TracePartitionedState {
    pub partitions: BTreeMap<TraceToken, AbstractState>,
    pub max_depth: usize,
}

impl TracePartitionedState {
    pub fn new(max_depth: usize) -> Self {
        Self {
            partitions: BTreeMap::new(),
            max_depth,
        }
    }

    pub fn singleton(init: AbstractState, max_depth: usize) -> Self {
        let mut partitions = BTreeMap::new();
        if !init.is_bottom() {
            partitions.insert(TraceToken::root(), init.refine_nat());
        }
        Self {
            partitions,
            max_depth,
        }
    }

    /// Inserts or joins `state` into the bucket for `token`.
    pub fn record(&mut self, token: TraceToken, state: AbstractState) {
        let refined = state.refine_nat();
        if refined.is_bottom() {
            return;
        }
        self.partitions
            .entry(token)
            .and_modify(|existing| *existing = existing.join(&refined).refine_nat())
            .or_insert(refined);
    }

    /// Collapses all trace partitions into a single summary `AbstractState` via lattice `join`.
    pub fn collapse(&self) -> AbstractState {
        let mut acc = AbstractState::bottom();
        for state in self.partitions.values() {
            acc = acc.join(state);
        }
        acc.refine_nat()
    }

    /// Pointwise join of two trace-partitioned states.
    pub fn join(&self, other: &Self) -> Self {
        let max_depth = self.max_depth.max(other.max_depth);
        let mut out = self.clone();
        out.max_depth = max_depth;
        for (tok, st) in &other.partitions {
            out.record(tok.clone(), *st);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lattice::{AbstractSign, IntervalBound};

    #[test]
    fn test_bourdoncle_wto_nested_loops() {
        // Classic nested loop CFG:
        // 0 -> 1 (outer loop head)
        // 1 -> 2 (inner loop head), 1 -> 3 (exit)
        // 2 -> 2 (inner self-loop), 2 -> 1 (back-edge to outer head)
        let adj = vec![
            vec![1],       // 0
            vec![2, 3],    // 1
            vec![2, 1],    // 2
            vec![],        // 3
        ];
        let wto = WtoOrdering::from_adjacency(&adj, 0);
        assert_eq!(wto.num_vertices, 4);
        assert_eq!(
            wto.elements,
            vec![
                WtoElement::Vertex(0),
                WtoElement::Component {
                    head: 1,
                    body: vec![WtoElement::Component {
                        head: 2,
                        body: vec![],
                    }],
                },
                WtoElement::Vertex(3),
            ]
        );
    }

    #[test]
    fn test_bourdoncle_wto_fixpoint_with_thresholds() {
        // 0 (entry: x = 0) -> 1 (loop head: x <= 99 -> x + 1) -> 2 (exit: x)
        let adj = vec![
            vec![1],    // 0
            vec![1, 2], // 1 (self-loop + exit to 2)
            vec![],     // 2
        ];
        let wto = WtoOrdering::from_adjacency(&adj, 0);
        let init = vec![
            AbstractState::const_nat(0),
            AbstractState::bottom(),
            AbstractState::bottom(),
        ];
        let thresholds = vec![0, 1, 50, 99, 100, 101];
        let solved = wto.solve_fixpoint(
            &init,
            |v, states| match v {
                0 => AbstractState::const_nat(0),
                1 => {
                    let from_entry = states[0];
                    let from_back = if let Some(iv) = states[1].interval {
                        if iv.min <= iv.max && iv.min <= 99 {
                            let capped_hi = iv.max.min(99);
                            AbstractState {
                                sign: AbstractSign::Positive,
                                interval: Some(IntervalBound::new(iv.min + 1, capped_hi + 1)),
                                ..AbstractState::top()
                            }
                        } else {
                            AbstractState::bottom()
                        }
                    } else {
                        AbstractState::bottom()
                    };
                    from_entry.join(&from_back)
                }
                2 => states[1],
                _ => AbstractState::bottom(),
            },
            &thresholds,
            1,
            12,
        );
        assert_eq!(solved[1].interval, Some(IntervalBound::new(0, 100)));
        assert_eq!(solved[2].interval, Some(IntervalBound::new(0, 100)));
    }

    #[test]
    fn test_trace_partitioned_state_preserves_branch_correlation() {
        let mut tp = TracePartitionedState::new(2);
        let root = TraceToken::root();
        let t_true = root.push_branch(1, 2);
        let t_false = root.push_branch(0, 2);

        tp.record(t_true.clone(), AbstractState::const_nat(10));
        tp.record(t_false.clone(), AbstractState::const_nat(90));
        assert_eq!(tp.partitions.len(), 2);
        assert_eq!(
            tp.partitions.get(&t_true).unwrap().interval,
            Some(IntervalBound::new(10, 10))
        );
        assert_eq!(
            tp.partitions.get(&t_false).unwrap().interval,
            Some(IntervalBound::new(90, 90))
        );

        let collapsed = tp.collapse();
        assert_eq!(collapsed.interval, Some(IntervalBound::new(10, 90)));
    }
}
