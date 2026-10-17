/-
-------------------------------------------------------------------------------
Stage 2: BFS-Lex Coordinate System (GloLex)
-------------------------------------------------------------------------------
-/

inductive GloLex (G : FiniteGraph) (delta : Nat) : (d : Nat) → (v : Nat) → Type where
  | root (r : Nat) (h_vert : r ∈ G.vertices) : GloLex G delta 0 r
  | childOf {d parent curr : Nat}
      (p : GloLex G delta d parent)
      (h_adj : G.Adj parent curr) : GloLex G delta (d + 1) curr
  | sameLayerNeighbor {d peer curr : Nat}
      (p : GloLex G delta d peer)
      (h_adj : G.Adj peer curr) : GloLex G delta d curr

namespace GloLex

variable {G : FiniteGraph} {delta : Nat}

def pathLength {d v : Nat} : GloLex G delta d v → Nat
  | root _ _ => 0
  | childOf p _ => pathLength p + 1
  | sameLayerNeighbor p _ => pathLength p

def toVertex {d v : Nat} (_ : GloLex G delta d v) : Nat := v

def toDist {d v : Nat} (_ : GloLex G delta d v) : Nat := d

end GloLex


/-
-------------------------------------------------------------------------------
Stage 3: GLONodes and GraphLevelOrder Architecture
-------------------------------------------------------------------------------
-/

structure GLONode where
  dist               : Nat
  lexId              : Nat
  out_neighbors      : List Nat
  interior_neighbors : List Nat
  exterior_neighbors : List Nat
  back_neighbors     : List Nat
  parent             : Option Nat × Option Nat
  toNumber           : Nat
  deriving Inhabited, BEq, Repr, Hashable

def GLONode.toProd (u : GLONode) : Nat × Nat :=
  (u.dist, u.lexId)

def GLONode.toCoords (v : GLONode) : Nat × Nat :=
  (v.dist, v.lexId)

def defaultGLONode : GLONode := {
  dist := 0,
  lexId := 0,
  out_neighbors := [],
  interior_neighbors := [],
  exterior_neighbors := [],
  back_neighbors := [],
  parent := (none, none),
  toNumber := 0
}

def GLONode.Lt (a b : GLONode) : Prop :=
  a.dist < b.dist ∨ (a.dist = b.dist ∧ a.lexId < b.lexId)

theorem gloNode_lt_wellFounded : WellFounded GLONode.Lt := by
  let f := GLONode.toProd
  apply Subrelation.wf (r := fun a b => Prod.Lex Nat.lt Nat.lt (f a) (f b))
  · intro a b h
    rcases h with h_dist | ⟨h_eq, h_id⟩
    · exact .left _ _ h_dist
    · dsimp [f, GLONode.toProd]  -- Unfold both f and GLONode.toProd
      rw [h_eq]                   -- Now a.dist is visible and can be rewritten to b.dist
      exact .right b.dist h_id  -- or simply: exact .right _ h_id
  · exact InvImage.wf f (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- Graph structured as layers of GLONodes under BFS-Lex with adjacency matrix representation -/
structure GraphLevelOrder where
  nodes            : Array GLONode
  delta            : Nat
  max_layer        : Nat
  graph            : FiniteGraph
  deriving Inhabited

instance : EmptyCollection GraphLevelOrder where
  emptyCollection := {
    nodes := #[],
    delta := 0,
    max_layer := 0,
    graph := default
  }


/-
-------------------------------------------------------------------------------
Stage 4: Interior and Exterior Neighbors & Formal Theorems
-------------------------------------------------------------------------------
-/

/-
-------------------------------------------------------------------------------
Stage 4: Interior and Exterior Neighbors & Formal Theorems
-------------------------------------------------------------------------------
-/

def interiorNeighbors (graph : GraphLevelOrder) (u v : GLONode) : Finset Nat :=
  if graph.nodes.contains u && graph.nodes.contains v && decide (v.dist > u.dist) && v.dist - u.dist == 1 then
    let u_fir_nbrs := u.out_neighbors
    let v_fir_nbrs := v.out_neighbors
    (u_fir_nbrs.inter v_fir_nbrs).toFinset
  else
    ∅

def exteriorNeighbors (G : GraphLevelOrder) (u v : GLONode) : Finset Nat :=
  if G.nodes.contains u && G.nodes.contains v && decide (v.dist > u.dist) && v.dist - u.dist == 1 then
    let u_sec_nbrs := (FiniteGraph.getN2Finset (G.graph) u.lexId)
    let v_fir_nbrs := (v.out_neighbors.toFinset)
    (u_sec_nbrs ∩ v_fir_nbrs)
  else
    ∅ -- Must be Finset.empty (∅) instead of []

/-- Back arcs leaving v: arcs (v, w) with w in a layer strictly before v's. -/
def backArcsOf (G : GraphLevelOrder) (v : GLONode) : Finset (Nat × Nat) :=
  ((G.nodes.filter (fun w =>
      w.dist < v.dist && v.out_neighbors.contains w.lexId)
    ).toList.map (fun w => (v.lexId, w.lexId))).toFinset

/-- back(u, v): for a forward arc u → v (v exactly one layer after u),
    the set of back arcs from v into earlier layers. -/
def backNeighb1ors (G : GraphLevelOrder) (u v : GLONode) : Finset (Nat × Nat) :=
  if G.nodes.contains u && G.nodes.contains v
      && u.out_neighbors.contains v.lexId
      && v.dist == u.dist + 1 then
    backArcsOf G v
  else
    ∅


theorem interior_neighbors_implies_first_neighbors (graph : GraphLevelOrder) (u v w : GLONode)
    (h_cond : graph.nodes.contains u && graph.nodes.contains v &&
              decide (v.dist > u.dist) && v.dist - u.dist == 1) :
    w.lexId ∈ interiorNeighbors graph u v →
    w.lexId ∈ u.out_neighbors ∧ w.lexId ∈ v.out_neighbors := by
  unfold interiorNeighbors
  rw [if_pos h_cond]
  intro h
  simpa [List.mem_toFinset, List.inter, List.mem_filter] using h


theorem exterior_neighbor_implies_second_neighbor (G : GraphLevelOrder) (u v w : GLONode)
    (h_cond : G.nodes.contains u && G.nodes.contains v && decide (v.dist > u.dist) && v.dist - u.dist == 1)
    (hw : w.lexId ∈ exteriorNeighbors G u v) :
    w.lexId ∈ FiniteGraph.getN2Finset G.graph u.lexId := by
  -- 1. Unfold exteriorNeighbors and evaluate the if condition
  unfold exteriorNeighbors at hw
  rw [if_pos h_cond] at hw

  -- 2. Simplify the let bindings and apply Finset intersection membership
  dsimp only at hw
  rw [Finset.mem_inter] at hw

  -- 3. Extract the first part of the conjunction (membership in u's second-order neighbor finset)
  rcases hw with ⟨h_u_sec, _⟩

  -- 4. Exact match!
  exact h_u_sec

end GraphLevelOrder
