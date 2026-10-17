/-
-------------------------------------------------------------------------------
Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/

-- 1. Define what makes a GraphLevelOrder a counterexample
def IsCounterexample (G : GraphLevelOrder) (violation_node : GLONode) : Prop :=
  G.graph.IsOriented ∧
  violation_node ∈ G.nodes ∧
  G.graph.isNonSeymour violation_node.lexId = true

-- 2. Define minimality over any other graph satisfying the counterexample condition
def IsMinimumCounterexample (G : GraphLevelOrder) (violation_node : GLONode) : Prop :=
  IsCounterexample G violation_node ∧
  ∀ (other : GraphLevelOrder) (other_node : GLONode) (u v : GLONode),
    IsCounterexample other other_node →
    (interiorNeighbors other u v).card < (interiorNeighbors G u v).card → False
