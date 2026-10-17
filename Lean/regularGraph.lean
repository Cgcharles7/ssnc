/-
-------------------------------------------------------------------------------
Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/

-- 1. Define what makes a GraphLevelOrder a counterexample
def IsCounterexample (G : GraphLevelOrder) : Prop :=
  G.graph.IsOriented ∧
  G.graph.vertices.Nonempty ∧
  (∀ n ∈ G.nodes, n.out_neighbors.toFinset = G.graph.getN1Finset n.lexId) ∧
  ∀ x ∈ G.graph.vertices, G.graph.isNonSeymour x = true

-- 2. Define minimality over any other graph satisfying the counterexample condition
def IsMinimumCounterexample (G : GraphLevelOrder) (violation_node : GLONode) : Prop :=
  IsCounterexample G violation_node ∧
  ∀ (other : GraphLevelOrder) (other_node : GLONode) (u v : GLONode),
    IsCounterexample other other_node →
    (interiorNeighbors other u v).card < (interiorNeighbors G u v).card → False
