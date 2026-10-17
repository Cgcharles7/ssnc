/-
-------------------------------------------------------------------------------
Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/
/-- Layer of the node with id x (assumes ids are looked up globally). -/
def distOf (G : GraphLevelOrder) (x : Nat) : Option Nat :=
  (G.nodes.find? (fun n => n.lexId == x)).map (·.dist)

/-- Forward arc u → v with v exactly one layer after u. -/
def fwdArc (G : GraphLevelOrder) (u v : GLONode) : Bool :=
  G.nodes.contains u && G.nodes.contains v
    && u.out_neighbors.contains v.lexId && v.dist == u.dist + 1

def IsCounterexample (G : GraphLevelOrder) : Prop :=
  G.graph.IsOriented ∧
  G.graph.vertices.Nonempty ∧
  (∀ n ∈ G.nodes, n.out_neighbors.toFinset = G.graph.getN1Finset n.lexId) ∧
  ∀ x ∈ G.graph.vertices, G.graph.isNonSeymour x = true

/-- Total interior arcs: sum of |int(u,v)| over forward arcs u → v. -/
def interiorArcCount (G : GraphLevelOrder) : Nat :=
  G.nodes.foldl (fun acc u =>
    G.nodes.foldl (fun acc' v =>
      acc' + (if fwdArc G u v then (interiorNeighbors G u v).card else 0)) acc) 0

def IsMinimumCounterexample (G : GraphLevelOrder) : Prop :=
  IsCounterexample G ∧
  ∀ H : GraphLevelOrder, IsCounterexample H →
    interiorArcCount G ≤ interiorArcCount H
