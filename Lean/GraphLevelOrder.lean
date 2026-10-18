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
abbrev Coord := Nat × Nat   -- (dist, lexId)


structure GLONode where
  dist               : Nat
  lexId              : Nat
  out_neighbors      : List Coord
  interior_neighbors : List Coord
  exterior_neighbors : List Coord
  back_neighbors     : List Coord
  parent             : Option Coord
  toNumber           : Nat
  deriving Inhabited, BEq, Repr, Hashable, DecidableEq

namespace GLONode

def toProd (u : GLONode) : Nat × Nat :=
  (u.dist, u.lexId)

def toCoords (v : GLONode) : Coord :=
  (v.dist, v.lexId)

def Lt (a b : GLONode) : Prop :=
  a.dist < b.dist ∨ (a.dist = b.dist ∧ a.lexId < b.lexId)

end GLONode

def defaultGLONode : GLONode := {
  dist := 0,
  lexId := 0,
  out_neighbors := [],
  interior_neighbors := [],
  exterior_neighbors := [],
  back_neighbors := [],
  parent := (none),
  toNumber := 0
}

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
namespace GraphLevelOrder

def getNode? (G : GraphLevelOrder) (c : Coord) : Option GLONode :=
  G.nodes.find? (fun u => u.dist == c.1 && u.lexId == c.2)

def getN1Finset (G : GraphLevelOrder) (c : Coord) : Finset Coord :=
  match getNode? G c with
  | some u => u.out_neighbors.toFinset
  | none   => ∅

def cardN1 (G : GraphLevelOrder) (c : Coord) : Nat :=
  (getN1Finset G c).card

def getN2Finset (G : GraphLevelOrder) (c : Coord) : Finset Coord :=
  let n1 := getN1Finset G c
  (n1.biUnion (fun v => getN1Finset G v)).filter (fun w => w ≠ c ∧ w ∉ n1)

def cardN2 (G : GraphLevelOrder) (c : Coord) : Nat :=
  (getN2Finset G c).card

def isSeymour (G : GraphLevelOrder) (c : Coord) : Bool :=
  decide (cardN1 G c ≤ cardN2 G c)

def isNonSeymour (G : GraphLevelOrder) (c : Coord) : Bool :=
  decide (cardN2 G c < cardN1 G c)

def IsIrreflexive (G : GraphLevelOrder) : Prop :=
  ∀ u ∈ G.nodes, u.toCoords ∉ u.out_neighbors

/-- Arc between nodes, by coordinate. -/
def Adj (G : GraphLevelOrder) (u v : GLONode) : Prop :=
  u ∈ G.nodes ∧ v ∈ G.nodes ∧ v.toCoords ∈ u.out_neighbors

/-- No 2-cycles: u → v excludes v → u. -/
def IsAntisymmetric (G : GraphLevelOrder) : Prop :=
  ∀ u v, G.Adj u v → u.toCoords ∉ v.out_neighbors

def IsOriented (G : GraphLevelOrder) : Prop :=
  G.IsIrreflexive ∧ G.IsAntisymmetric

def CoordUnique (G : GraphLevelOrder) : Prop :=
  ∀ a ∈ G.nodes, ∀ b ∈ G.nodes,
    a.dist = b.dist → a.lexId = b.lexId → a = b

theorem getN1Finset_eq (G : GraphLevelOrder) (hu : G.CoordUnique)
    (n : GLONode) (hn : n ∈ G.nodes) :
    getN1Finset G n.toCoords = n.out_neighbors.toFinset := by
  -- 1. find? succeeds, because n itself satisfies the predicate
  have hsome : (G.nodes.find? (fun u =>
      u.dist == n.toCoords.1 && u.lexId == n.toCoords.2)).isSome = true := by
    rw [Array.find?_isSome]
    exact ⟨n, hn, by simp [GLONode.toCoords]⟩
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  -- 2. whatever it found is a node of G satisfying the predicate
  have hmem : m ∈ G.nodes := Array.mem_of_find?_eq_some hm
  have hpred := Array.find?_some hm
  simp [GLONode.toCoords] at hpred          -- hpred : m.dist = n.dist ∧ m.lexId = n.lexId
  -- 3. coordinate uniqueness gives m = n
  have hmn : m = n := hu m hmem n hn hpred.1 hpred.2
  -- 4. unfold and rewrite
  unfold getN1Finset getNode?
  rw [hm]
  subst hmn
  rfl

theorem cardN1_eq (G : GraphLevelOrder) (hu : G.CoordUnique)
    (n : GLONode) (hn : n ∈ G.nodes) :
    cardN1 G n.toCoords = n.out_neighbors.toFinset.card := by
  unfold cardN1; rw [getN1Finset_eq G hu n hn]

theorem cardN1_eq_length (G : GraphLevelOrder) (hu : G.CoordUnique)
    (n : GLONode) (hn : n ∈ G.nodes) (hnd : n.out_neighbors.Nodup) :
    cardN1 G n.toCoords = n.out_neighbors.length := by
  rw [cardN1_eq G hu n hn, List.toFinset_card_of_nodup hnd]
/-
-------------------------------------------------------------------------------
Stage 4: Interior and Exterior Neighbors & Formal Theorems
-------------------------------------------------------------------------------
-/


def interiorNeighbors (G : GraphLevelOrder) (u v : GLONode) : Finset Coord :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    u.out_neighbors.toFinset ∩ v.out_neighbors.toFinset
  else
    ∅

def exteriorNeighbors (G : GraphLevelOrder) (u v : GLONode) : Finset Coord :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    getN2Finset G u.toCoords ∩ v.out_neighbors.toFinset
  else
    ∅

def backNeighbors (G : GraphLevelOrder) (u v : GLONode) : Finset Coord :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    v.out_neighbors.toFinset.filter (·.1 < v.dist)
  else ∅


theorem interior_neighbors_implies_first_neighbors
    (G : GraphLevelOrder) (u v : GLONode) (c : Coord)
    (h_cond : (G.nodes.contains u && G.nodes.contains v
               && v.dist == u.dist + 1) = true) :
    c ∈ interiorNeighbors G u v →
    c ∈ u.out_neighbors ∧ c ∈ v.out_neighbors := by
  unfold interiorNeighbors
  rw [if_pos h_cond]
  intro h
  simpa [Finset.mem_inter, List.mem_toFinset] using h


theorem exterior_neighbor_implies_second_neighbor
    (G : GraphLevelOrder) (u v : GLONode) (c : Coord)
    (h_cond : (G.nodes.contains u && G.nodes.contains v
               && v.dist == u.dist + 1) = true)
    (hc : c ∈ exteriorNeighbors G u v) :
    c ∈ getN2Finset G u.toCoords := by
  unfold exteriorNeighbors at hc
  rw [if_pos h_cond] at hc
  exact (Finset.mem_inter.mp hc).1

end GraphLevelOrder




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

  -- 4. Exact match!theorem layer_bound_of_step (s : Nat → Nat) (δ : Nat)
    (h1 : s 1 = δ) (hstep : ∀ j, 1 ≤ j → s (j + 1) ≤ s j - 1) :
    ∀ m, s (m + 2) ≤ δ - (m + 1) := by
  intro m
  induction m with
  | zero =>
    have h : s 2 ≤ s 1 - 1 := hstep 1 le_rfl
    show s 2 ≤ δ - (0 + 1)
    omega
  | succ m ih =>
    have h : s (m + 3) ≤ s (m + 2) - 1 := hstep (m + 2) (by omega)
    show s (m + 3) ≤ δ - (m + 1 + 1)
    omega

theorem degree_formula_under_no_back_arcs
    (g : GraphLevelOrder) (delta : Nat) (h_delta : delta = g.delta)
    (h_all_non_seymour : ∀ u ∈ g.nodes.toList, g.isNonSeymour u.dist u.lexId = true)
    (k : Nat)
    (h_no_back_upto : ∀ x ∈ g.nodes, x.dist ≤ k → ∀ y ∈ g.nodes, y.dist = k + 1 → g.backNeighbors x y = ∅)
    (h0 : Fintype.card (getLayerAtDistance g 0) = 1)
    (h1 : Fintype.card (getLayerAtDistance g 1) = delta)
    (h_step : ∀ j, 1 ≤ j →
      Fintype.card (getLayerAtDistance g (j + 1))
        ≤ Fintype.card (getLayerAtDistance g j) - 1)
    (m : Nat) :
    Fintype.card (getLayerAtDistance g (m + 2)) ≤ delta - (m + 1) :=
  layer_bound_of_step (fun j => Fintype.card (getLayerAtDistance g j)) delta h1 h_step m

  exact h_u_sec

end GraphLevelOrder


