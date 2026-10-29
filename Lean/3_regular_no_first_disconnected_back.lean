import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Basic

/-
-------------------------------------------------------------------------------
Stage 1: Finite Graph & Seymour Conjecture Primitives
-------------------------------------------------------------------------------
-/

structure FiniteGraph where
  vertices : Finset Nat
  edges : Finset (Nat × Nat)
  edge_valid : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices

namespace FiniteGraph

/-- Adjacency predicate derived from the edge finset -/
def Adj (G : FiniteGraph) (u v : Nat) : Prop :=
  (u, v) ∈ G.edges

instance (G : FiniteGraph) (u v : Nat) : Decidable (G.Adj u v) :=
  Finset.decidableMem (u, v) G.edges

def getN1Finset (G : FiniteGraph) (u : Nat) : Finset Nat :=
  (G.edges.filter (fun e => e.1 = u)).image (fun e => e.2)

def cardN1 (G : FiniteGraph) (u : Nat) : Nat :=
  (getN1Finset G u).card

def getN2Finset (G : FiniteGraph) (u : Nat) : Finset Nat :=
  let n1 := getN1Finset G u
  let all_n2 := n1.biUnion (fun v => getN1Finset G v)
  all_n2.filter (fun w => w ≠ u ∧ w ∉ n1)

def cardN2 (G : FiniteGraph) (u : Nat) : Nat :=
  (getN2Finset G u).card

def isSeymour (G : FiniteGraph) (u : Nat) : Bool :=
  cardN2 G u ≥ cardN1 G u

def isNonSeymour (G : FiniteGraph) (u : Nat) : Bool :=
  cardN2 G u < cardN1 G u

def IsIrreflexive (G : FiniteGraph) : Prop :=
  ∀ u ∈ G.vertices, ¬ G.Adj u u

def IsAntisymmetric (G : FiniteGraph) : Prop :=
  ∀ u v, G.Adj u v → G.Adj v u → u = v

/-- An oriented graph is irreflexive and antisymmetric (no 2-cycles) -/
def IsOriented (G : FiniteGraph) : Prop :=
  G.IsIrreflexive ∧ G.IsAntisymmetric

def IsSeymourProp (G : FiniteGraph) (u : Nat) : Prop :=
  cardN1 G u ≤ cardN2 G u

lemma isSeymour_iff (G : FiniteGraph) (u : Nat) :
    G.isSeymour u = true ↔ G.IsSeymourProp u := by
  dsimp [isSeymour, IsSeymourProp]
  rw [Bool.decide_iff]

-- First, give FiniteGraph a default (empty) instance
instance : Inhabited FiniteGraph where
  default := {
    vertices := ∅,
    edges := ∅,
    edge_valid := by
      intro e he
      -- Since edges is empty, any membership `he` is a contradiction
      simp at he
  }

end FiniteGraph

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
  deriving Inhabited, Repr, Hashable, DecidableEq

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
    && u.out_neighbors.contains v.toCoords && v.dist == u.dist + 1

def IsCounterexample (G : GraphLevelOrder) : Prop :=
  G.CoordUnique ∧
  G.IsOriented ∧
  0 < G.nodes.size ∧
  ∀ x ∈ G.nodes, G.isNonSeymour (x.dist, x.lexId) = true

def layerInteriorArcCount (G : GraphLevelOrder) (k : Nat) : Nat :=
  G.nodes.foldl (fun acc u =>
    if u.dist == k then
      G.nodes.foldl (fun acc' v =>
        acc' + (if fwdArc G u v then (G.interiorNeighbors u v).card else 0)) acc
    else acc) 0

/-- Total interior arcs: sum of |int(u,v)| over forward arcs u → v. -/
def interiorArcCount (G : GraphLevelOrder) : Nat :=
  G.nodes.foldl (fun acc u =>
    G.nodes.foldl (fun acc' v =>
      acc' + (if fwdArc G u v then (G.interiorNeighbors u v).card else 0)) acc) 0

def getLayerAtDistance (g : GraphLevelOrder) (k : Nat) : Finset (GLONode) :=
  -- Assuming g.nodes has a conversion to Finset or is a Finset/List
  (g.nodes.toList.filter (fun u => u.dist == k)).toFinset

/-- Neighborhood density at layer k, defined as the ratio of interior arcs to layer size. -/
def neighborhood_density (G : GraphLevelOrder) (k : Nat) : Rat :=
  let layerSize := (getLayerAtDistance G k).card
  let arcCount := layerInteriorArcCount G k
  if layerSize = 0 then 0
  else (arcCount : Rat) / (layerSize : Rat)

def interiorInDegree (G : GraphLevelOrder) (u v : GLONode) (k : Nat) : Finset GLONode :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    (G.nodes.filter (fun w => w.toCoords ∈ v.out_neighbors ∧ w.dist = k)).toList.toFinset
  else
    ∅

def interiorOutDegree (G : GraphLevelOrder) (u v : GLONode) (k : Nat) : Finset GLONode :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    -- Filter the graph nodes and convert the resulting Array to a Finset GLONode
    (G.nodes.filter (fun w => w.toCoords ∈ v.out_neighbors ∧ w.dist = k)).toList.toFinset
  else
    ∅

def totalInteriorDegree (G : GraphLevelOrder) (u v : GLONode) (k : Nat): Finset GLONode :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    interiorInDegree G u v k ∪ interiorOutDegree G u v k
  else
    ∅

def maxTotalInteriorDegree (G : GraphLevelOrder) (k : Nat) : Nat :=
  G.nodes.foldl (fun maxVal u =>
    if u.dist == k then
      G.nodes.foldl (fun innerMax v =>
        if v.dist == u.dist + 1 then
          max innerMax (totalInteriorDegree G u v k).card
        else
          innerMax
      ) maxVal
    else
      maxVal
  ) 0

def mceMetric (G : GraphLevelOrder) (k : Nat) : Nat × Nat :=
  (interiorArcCount G, maxTotalInteriorDegree G k)

def IsMinimumCounterexample (G : GraphLevelOrder) : Prop :=
  IsCounterexample G ∧
  ∀ H : GraphLevelOrder, IsCounterexample H →
    mceMetric G ≤ mceMetric H

/-- A graph is cycle-packed if every node has balanced interior degrees
    (in-degree 1, out-degree 1) resulting in a total interior degree of exactly 2. -/

--def IsCyclePacked (G : GraphLevelOrder) : Prop :=
--  ∀ u ∈ G.nodes,
--    interiorInDegree G u u.dist = 1 ∧
--    interiorOutDegree G u u.dist = 1 ∧
--    totalInteriorDegree G u u.dist = 2

-- Check/Proof that any valid node in the graph satisfies out-degree ≥ delta
lemma node_out_degree_ge_delta
    (g : GraphLevelOrder)
    (u : GLONode)
    (hu_in : u ∈ g.nodes.toList)
    (delta : Nat)
    (h_min : ∀ x ∈ g.nodes.toList, delta ≤ x.out_neighbors.length) :
    delta ≤ u.out_neighbors.length := by
  -- Unfold the definition of minOutDegree or invoke your graph's minimum degree invariant
  -- Use the property that minOutDegree is less than or equal to the degree of any node in the list
  exact h_min u hu_in

theorem internal_degree_lower_bound
  {n : Nat}
  (g : GraphLevelOrder)
  (ui : GLONode)
  (i : Nat)
  (h_layer : ui.dist = i) -- ui.dist.val is a Nat
  (h_ui_in : ui ∈ g.nodes.toList)
  (h_min_degree : ∀ v ∈ g.nodes.toList, v.out_neighbors.length ≥ v.dist) :
  ui.out_neighbors.length ≥ i := by

  -- 1. Apply the minimum degree hypothesis to ui
  have h_bound := h_min_degree ui h_ui_in

  -- 2. Substitute ui.dist.val = i into the bound using rw
  rw [h_layer] at h_bound

  -- 3. Exact match finishes the proof
  exact h_bound

theorem interior_degree_rigidity
  (g : GraphLevelOrder)
  (u : GLONode)
  (k : Nat)
  (h_layer : u.dist = k)
  (h_u_in : u ∈ g.nodes.toList)
  -- Suppose we have a quantity representing the interior neighbor count / degree of u
  -- (e.g., sum of sizes of interiorNeighbors with forward children)
  (int_count : Nat)
  -- Hypotheses representing your MCE constraints:
  (h_not_too_low : int_count < k → False) -- Too low forces another forward arc / violates structure
  (h_not_too_high : k < int_count → False) -- Too high violates MCE conditions / non-Seymour bounds
  : int_count = k := by
  -- Trichotomy: either int_count < k, int_count = k, or int_count > k
  rcases lt_trichotomy int_count k with h_lt | h_eq | h_gt
  · -- Case 1: int_count < k (Too low)
    exfalso
    exact h_not_too_low h_lt
  · -- Case 2: int_count = k (The exact target equality)
    exact h_eq
  · -- Case 3: int_count > k (Too high)
    exfalso
    exact h_not_too_high h_gt

theorem node_interior_degree_eq_k
  (g : GraphLevelOrder)
  (u : GLONode)
  (k : Nat)
  (h_layer : u.dist = k)
  (h_u_in : u ∈ g.nodes.toList)
  (mce : IsMinimumCounterexample g)
  -- Let's say int_deg is the total interior neighbors in layer k+1
  (int_deg : Nat)
  (h_lower_bound : k ≤ int_deg) -- Derived from min-degree / no-back-arcs
  (h_upper_bound : int_deg ≤ k) -- Derived from non-Seymour / MCE constraints
  : int_deg = k := by
  omega
/-
-------------------------------------------------------------------------------
--Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/

-- /-- Two nodes u and v are connected by a back-path/arc if there is a node x
--     in v's back-neighbors that is also an out-neighbor of u. -/
def ConnectedBack (G : GraphLevelOrder) (u v : GLONode) : Prop :=
  ∃ x ∈ G.backNeighbors u v, x ∈ u.out_neighbors

-- /-- A graph has no connected back-arcs if no forward arc
--     coexists with a connected back-arc structure. -/
def NoConnectedBack (G : GraphLevelOrder) : Prop :=
  ∀ u v, fwdArc G u v = true → ¬ ConnectedBack G u v

def IsRoot (G : GraphLevelOrder) (r : GLONode) : Prop :=
  r ∈ G.nodes ∧ ∀ n ∈ G.nodes, n ≠ r → GLONode.Lt r n

theorem root_unique (G : GraphLevelOrder) (r₁ r₂ : GLONode)
    (h1 : IsRoot G r₁) (h2 : IsRoot G r₂) : r₁ = r₂ := by
  by_contra hne
  have a := h1.2 r₂ h2.1 (Ne.symm hne)   -- Lt r₁ r₂
  have b := h2.2 r₁ h1.1 hne             -- Lt r₂ r₁
  unfold GLONode.Lt at a b
  omega

/-- The least node sits in layer 0, provided layer 0 is nonempty. -/
theorem root_dist_zero (G : GraphLevelOrder) (r : GLONode) (hr : IsRoot G r)
    (h0 : ∃ n ∈ G.nodes, n.dist = 0) : r.dist = 0 := by
  obtain ⟨n, hn, hn0⟩ := h0
  by_cases h : n = r
  · subst h; exact hn0
  · have := hr.2 n hn h
    unfold GLONode.Lt at this
    omega

theorem layer_bound_of_step (s : Nat → Nat) (δ : Nat)
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
    (g : GraphLevelOrder) (delta : Nat)
    (h_all_non_seymour : ∀ u ∈ g.nodes.toList, g.isNonSeymour (u.dist, u.lexId) = true)
    (k : Nat)
    (h_no_back_upto : ∀ x ∈ g.nodes, x.dist ≤ k → ∀ y ∈ g.nodes, y.dist = k + 1 → g.backNeighbors x y = ∅)
    (h0 : Fintype.card (getLayerAtDistance g 0) = 1)
    (h1 : Fintype.card (getLayerAtDistance g 1) = delta)
    (h_step : ∀ j, 1 ≤ j →
      Fintype.card (getLayerAtDistance g (j + 1))
        = Fintype.card (getLayerAtDistance g j) - 1)
    (m : Nat) :
    Fintype.card (getLayerAtDistance g (m + 2)) = delta - (m + 1) := by
  induction m with
  | zero =>
    -- Base case: m = 0, we need to show layer 2 size ≤ delta - 1
    have h2 : Fintype.card (getLayerAtDistance g 2) = Fintype.card (getLayerAtDistance g 1) - 1 := h_step 1 le_rfl
    rw [h1] at h2
    rw [h2]
  | succ m ih =>
    -- Inductive step: assume result for m, prove for m + 1
    have h_next : Fintype.card (getLayerAtDistance g (m + 3)) = Fintype.card (getLayerAtDistance g (m + 2)) - 1 := h_step (m + 2) (by omega)
    rw [h_next]
    omega


def layerIds (G : GraphLevelOrder) (j : Nat) : Finset Nat :=
  ((G.nodes.filter (·.dist == j)).toList.map (·.lexId)).toFinset

def layerCoords (G : GraphLevelOrder) (j : Nat) : Finset Coord :=
  ((G.nodes.toList.filter (·.dist == j)).map (·.toCoords)).toFinset

def BFSWF (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, ∀ x ∈ v.out_neighbors,
    (∃ d ∈ G.nodes, d.toCoords = x) ∧ x.1 ≤ v.dist + 1

theorem fwdArc_spec (G : GraphLevelOrder) (u v : GLONode) :
    fwdArc G u v = true ↔
      u ∈ G.nodes ∧ v ∈ G.nodes ∧ v.toCoords ∈ u.out_neighbors
        ∧ v.dist = u.dist + 1 := by
  unfold fwdArc
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨hu, hv⟩, huv⟩, hd⟩
    exact ⟨Array.mem_of_contains_eq_true hu, Array.mem_of_contains_eq_true hv,
      List.mem_of_elem_eq_true huv, hd⟩
  · rintro ⟨hu, hv, huv, hd⟩
    exact ⟨⟨⟨Array.contains_eq_true_of_mem hu, Array.contains_eq_true_of_mem hv⟩,
      List.elem_eq_true_of_mem huv⟩, hd⟩

theorem exteriorNeighbors_subset_layer
    (G : GraphLevelOrder) (hu : G.CoordUnique) (hw : G.BFSWF)
    (u v : GLONode) (hfwd : fwdArc G u v = true)
    (hnb : G.backNeighbors u v = ∅)
    (hsame : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors) :
    G.exteriorNeighbors u v ⊆ G.layerCoords (v.dist + 1) := by
  obtain ⟨hu_mem, hv_mem, _, hd⟩ := (fwdArc_spec G u v).mp hfwd
  intro x hx
  have hguard : (G.nodes.contains u && G.nodes.contains v
      && v.dist == u.dist + 1) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨Array.contains_eq_true_of_mem hu_mem,
            Array.contains_eq_true_of_mem hv_mem⟩, hd⟩
  unfold exteriorNeighbors at hx
  rw [if_pos hguard] at hx
  obtain ⟨hN2, hxv⟩ := Finset.mem_inter.mp hx
  have hxv' : x ∈ v.out_neighbors := List.mem_toFinset.mp hxv
  -- x ∉ N1(u) = out(u)
  have hnotu : x ∉ u.out_neighbors := by
    have h := (Finset.mem_filter.mp hN2).2.2        -- x ∉ getN1Finset G u.toCoords
    rw [getN1Finset_eq G hu u hu_mem] at h
    simpa using h
  -- layer bounds
  have hle := (hw v hv_mem x hxv').2
  have hge : v.dist ≤ x.1 := by
    by_contra hlt
    have : x ∈ G.backNeighbors u v := by
      unfold backNeighbors; rw [if_pos hguard]
      simp [hxv', Nat.lt_of_not_le hlt]
    rw [hnb] at this; simp at this
  have hlay : x.1 = v.dist + 1 := by
    rcases Nat.lt_or_ge v.dist x.1 with h | h
    · omega
    · exact absurd (hsame x hxv' (by omega)) hnotu
  obtain ⟨⟨d, hd_mem, hd_eq⟩, _⟩ := hw v hv_mem x hxv'
  have hdd : d.dist = x.1 := by rw [← hd_eq]; rfl
  simp only [layerCoords, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨d, ⟨Array.mem_def.mp hd_mem, by omega⟩, hd_eq⟩

/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/

def IsMinOutDeg (G : GraphLevelOrder) (δ : Nat) : Prop :=
  (∀ x ∈ G.graph.vertices, δ ≤ G.graph.cardN1 x) ∧
  (∃ x ∈ G.graph.vertices, G.graph.cardN1 x = δ)

def NoBackArcs (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, ∀ u ∈ G.nodes, G.backNeighbors u v = ∅

theorem interior_lower_bound (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hback : backC = 0)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    k + 1 ≤ intC := by omega

/-- Back arcs forced by interior deficiency (no load balance, no minimality). -/
theorem back_ge_deficiency (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    (k + 1) - intC ≤ backC := by omega

theorem too_few_interior (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ)
    (hdef : intC < k + 1) : 0 < backC := by omega

theorem layers_disjoint
    (k1 k2 : Nat) (v_k1 v_k2 : GLONode)
    (h_dist1 : v_k1.dist = k1) (h_dist2 : v_k2.dist = k2)
    (h_neq : k1 ≠ k2) : v_k1 ≠ v_k2 := by
  intro h_eq
  apply h_neq
  rw [← h_dist1, ← h_dist2, h_eq]

theorem layerCoords_disjoint (G : GraphLevelOrder)
    (j₁ j₂ : Nat) (hne : j₁ ≠ j₂) :
    Disjoint (G.layerCoords j₁) (G.layerCoords j₂) := by
  rw [Finset.disjoint_left]
  intro c h1 h2
  simp only [GraphLevelOrder.layerCoords, List.mem_toFinset, List.mem_map, List.mem_filter,
    beq_iff_eq] at h1 h2
  obtain ⟨a, ⟨_, ha⟩, rfl⟩ := h1
  obtain ⟨b, ⟨_, hb⟩, hab⟩ := h2
  -- hab : b.toCoords = a.toCoords, so b.dist = a.dist
  have : b.dist = a.dist := congrArg Prod.fst hab
  omega

/-- Node-level consistency: out-neighbors split into back / interior / exterior. -/
def PartitionWF (n : GLONode) : Prop :=
  n.out_neighbors.length =
    n.back_neighbors.length + n.interior_neighbors.length + n.exterior_neighbors.length

lemma child_interior_deficit
    (child : GLONode) (k : Nat)
    (h_part : PartitionWF child)
    (h_deg : k ≤ child.out_neighbors.length)
    (h_int : child.interior_neighbors.length < k) :
    0 < child.back_neighbors.length ∨ 0 < child.exterior_neighbors.length := by
  unfold PartitionWF at h_part
  omega

/-
-------------------------------------------------------------------------------
--Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/
/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/

theorem out_eq_int_union_ext
    (G : GraphLevelOrder) (hu : G.CoordUnique) (hw : G.BFSWF)
    (k : Nat) (u v : GLONode)
    (hfwd : fwdArc G u v = true)
    (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hno_same : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors) :
    v.out_neighbors.toFinset
      = G.interiorNeighbors u v ∪ G.exteriorNeighbors u v := by
  obtain ⟨hu_node, hv_node, hadj, hdist⟩ := (fwdArc_spec G u v).mp hfwd
  -- hadj : v.toCoords ∈ u.out_neighbors  (shape assumed from fwdArc_spec)
  have hcond : (G.nodes.contains u && G.nodes.contains v
                && v.dist == u.dist + 1) = true := by
    simp [hu_node, hv_node, hdist]        -- Array.contains lemma names are version-sensitive
  ext x
  constructor
  · intro hx
    have hxv : x ∈ v.out_neighbors := List.mem_toFinset.mp hx
    have hle := (hw v hv_node x hxv).2
    -- no back arcs: x is not below v's layer
    have hge : v.dist ≤ x.1 := by
      by_contra hlt
      have : x ∈ G.backNeighbors u v := by
        unfold GraphLevelOrder.backNeighbors
        rw [if_pos hcond]
        simp [hxv]; omega
      rw [hnb] at this; simp at this
    by_cases heq : x.1 = v.dist
    · -- same layer as v: interior
      apply Finset.mem_union_left
      unfold GraphLevelOrder.interiorNeighbors
      rw [if_pos hcond]
      simp [hxv, hno_same x hxv heq]
    · -- layer v.dist + 1: exterior
      apply Finset.mem_union_right
      unfold GraphLevelOrder.exteriorNeighbors
      rw [if_pos hcond]
      refine Finset.mem_inter.mpr ⟨?_, by simpa using hxv⟩
      have hx2 : x.1 = u.dist + 2 := by omega
      unfold GraphLevelOrder.getN2Finset
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      refine ⟨⟨v.toCoords, ?_, ?_⟩, ?_, ?_⟩
      · rw [GraphLevelOrder.getN1Finset_eq G hu u hu_node]; simpa using hadj
      · rw [GraphLevelOrder.getN1Finset_eq G hu v hv_node]; simpa using hxv
      · intro h; have := congrArg Prod.fst h; simp [GLONode.toCoords] at this; omega
      · rw [GraphLevelOrder.getN1Finset_eq G hu u hu_node]
        intro hmem
        have := (hw u hu_node x (List.mem_toFinset.mp hmem)).2
        omega
  · intro hx
    rcases Finset.mem_union.mp hx with h | h
    · unfold GraphLevelOrder.interiorNeighbors at h
      rw [if_pos hcond] at h
      exact (Finset.mem_inter.mp h).2
    · unfold GraphLevelOrder.exteriorNeighbors at h
      rw [if_pos hcond] at h
      exact (Finset.mem_inter.mp h).2


theorem int_ext_disjoint (G : GraphLevelOrder) (hu : G.CoordUnique)
    (u v : GLONode) (hu_node : u ∈ G.nodes) :
    Disjoint (G.interiorNeighbors u v) (G.exteriorNeighbors u v) := by
  rw [Finset.disjoint_left]
  intro x hxi hxe
  by_cases hc : (G.nodes.contains u && G.nodes.contains v
                  && v.dist == u.dist + 1) = true
  · rw [interiorNeighbors, if_pos hc] at hxi
    rw [exteriorNeighbors, if_pos hc] at hxe
    have h1 : x ∈ u.out_neighbors.toFinset := (Finset.mem_inter.mp hxi).1
    have h2 := (Finset.mem_inter.mp hxe).1
    unfold getN2Finset at h2
    simp only [Finset.mem_filter] at h2
    rw [getN1Finset_eq G hu u hu_node] at h2
    exact h2.2.2 h1
  · rw [interiorNeighbors, if_neg hc] at hxi
    simp at hxi

theorem extra_forward_arc_produces_seymour_vertex
    (G : GraphLevelOrder) (hu : G.CoordUnique) (u v : GLONode)
    (h_cond : (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true)
    (hfwd : fwdArc G u v = true)
    (hu_deg : G.cardN1 u.toCoords = G.delta)
    (h_ext_bound : G.cardN1 u.toCoords ≤ (G.exteriorNeighbors u v).card) :
    G.cardN1 u.toCoords ≤ G.cardN2 u.toCoords := by
  -- 1. Show exteriorNeighbors G u v is a subset of getN2Finset G u.toCoords
  have h_sub : G.exteriorNeighbors u v ⊆ G.getN2Finset u.toCoords := by
    intro c hc
    exact exterior_neighbor_implies_second_neighbor G u v c h_cond hc

  -- 2. Take cardinalities: |exteriorNeighbors| <= |N2(u)|
  have h_card_le := Finset.card_le_card h_sub

  -- 3. Chain inequalities: |N1(u)| <= |exteriorNeighbors| <= |N2(u)|
  exact h_ext_bound.trans h_card_le

/-- A counterexample G with fewer/excess arcs breaking minimality
    contradicts the Minimum Counterexample H. -/
theorem extra_interior_violates_mce_metric
    (G H : GraphLevelOrder)
    (h_mce : IsMinimumCounterexample H)
    (h_G_counter : IsCounterexample G)
    (h_smaller_metric : mceMetric G < mceMetric H) :
    False := by
  obtain ⟨_, h_min⟩ := h_mce
  have h_le : mceMetric H ≤ mceMetric G := h_min G h_G_counter
  exact absurd h_smaller_metric (not_lt_of_ge h_le)

theorem int_not_too_low
    (δ k int_d fwd_d back_d : Nat)
    (h_deg   : δ ≤ int_d + fwd_d + back_d)   -- out-degree ≥ δ
    (h_noback : back_d = 0)
    (h_case1 : fwd_d + k ≤ δ)                -- case 1: no extra forward arcs
    : ¬ int_d < k := by
  intro h_low
  omega

lemma child_interior_deficit_no_back
    (G : GraphLevelOrder)
    (child : GLONode) (k : Nat)
    (h_part : PartitionWF child)
    (h_deg : G.delta ≤ child.out_neighbors.length)
    (h_no_back : child.back_neighbors.length = 0)
    (h_int : child.interior_neighbors.length < k) :
    G.delta < child.exterior_neighbors.length + k := by
  unfold PartitionWF at h_part
  omega

theorem fewer_interior_implies_extra_forward
    (G : GraphLevelOrder) (hu : G.CoordUnique) (u v : GLONode)
    (h_mce : IsMinimumCounterexample G)
    (h_cond : (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true)
    (hfwd : fwdArc G u v = true)
    (hu_deg : G.cardN1 u.toCoords = G.delta)
    (h_ext_bound : G.cardN1 u.toCoords ≤ (G.exteriorNeighbors u v).card) :
    G.cardN1 u.toCoords ≤ G.cardN2 u.toCoords := by
  -- 1. Show exteriorNeighbors G u v is a subset of getN2Finset G u.toCoords
  have h_sub : G.exteriorNeighbors u v ⊆ G.getN2Finset u.toCoords := by
    intro c hc
    exact exterior_neighbor_implies_second_neighbor G u v c h_cond hc

  -- 2. Take cardinalities: |exteriorNeighbors| <= |N2(u)|
  have h_card_le := Finset.card_le_card h_sub

  -- 3. Chain inequalities: |N1(u)| <= |exteriorNeighbors| <= |N2(u)|
  exact h_ext_bound.trans h_card_le

theorem interior_degree_bounds_strong
    (G : GraphLevelOrder) (hu : G.CoordUnique) (u v : GLONode)
    (h_mce : IsMinimumCounterexample G)
    (h_cond : (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true)
    (hfwd : fwdArc G u v = true)
    (hu_deg : G.cardN1 u.toCoords = G.delta)
    -- layer structure (hypotheses of degree_formula_under_no_back_arcs)
    (h_all_non_seymour : ∀ w ∈ G.nodes.toList, G.isNonSeymour (w.dist, w.lexId) = true)
    (k : Nat) (hk : 1 ≤ k) (hkδ : k ≤ G.delta) (hu_dist : u.dist = k)
    (h_no_back_upto : ∀ x ∈ G.nodes, x.dist ≤ k → ∀ y ∈ G.nodes, y.dist = k + 1 →
        G.backNeighbors x y = ∅)
    (h0 : Fintype.card (getLayerAtDistance G 0) = 1)
    (h1 : Fintype.card (getLayerAtDistance G 1) = G.delta)
    (h_step : ∀ j, 1 ≤ j →
        Fintype.card (getLayerAtDistance G (j + 1)) = Fintype.card (getLayerAtDistance G j) - 1)
    -- ASSUMED (needs proof): exterior neighbors of u via v live in layer k+1
    (h_ext_layer : (G.exteriorNeighbors u v).card ≤ Fintype.card (getLayerAtDistance G (k + 1)))
    -- ASSUMED definition: interior degree = N1 minus exterior neighbours
    (interiorDeg : ℕ)
    (h_int : interiorDeg = G.cardN1 u.toCoords - (G.exteriorNeighbors u v).card)
    -- ASSUMED reduction: interior degree above B yields a smaller counterexample
    (B : ℕ)
    (h_reduce : B < interiorDeg →
        ∃ H : GraphLevelOrder, IsCounterexample H ∧ mceMetric H < mceMetric G) :
    k ≤ interiorDeg ∧ interiorDeg ≤ B := by
  -- Layer k+1 has size δ - k, from the degree formula with m = k - 1
  have h_layer : Fintype.card (getLayerAtDistance G (k + 1)) = G.delta - k := by
    have h := degree_formula_under_no_back_arcs G G.delta h_all_non_seymour k
      h_no_back_upto h0 h1 h_step (k - 1)
    have e : k - 1 + 2 = k + 1 := by omega
    rw [e] at h
    omega
  constructor
  · -- Lower bound: at most δ - k exterior neighbours, so at least k interior ones
    rw [h_int, hu_deg]
    omega
  · -- Upper bound: otherwise a smaller counterexample contradicts minimality
    by_contra h_not
    obtain ⟨H, hH, hmetric⟩ := h_reduce (not_le.mp h_not)
    exact extra_interior_violates_mce_metric H G h_mce hH hmetric

theorem cond_of_nodes {G : GraphLevelOrder} {u v : GLONode}
    (hu : u ∈ G.nodes) (hv : v ∈ G.nodes) (hd : v.dist = u.dist + 1) :
    (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true := by
  simp [hu, hv, hd]

theorem mem_getN2Finset_iff (G : GraphLevelOrder) (c x : Coord) :
    x ∈ getN2Finset G c ↔
      (∃ a ∈ getN1Finset G c, x ∈ getN1Finset G a)
        ∧ x ≠ c ∧ x ∉ getN1Finset G c := by
  simp only [getN2Finset, Finset.mem_filter, Finset.mem_biUnion]

theorem out_subset_int_union_ext_general
    (G : GraphLevelOrder) (hu : G.CoordUnique)
    (u v : GLONode) (hu_node : u ∈ G.nodes) (hv_node : v ∈ G.nodes)
    (hadj : v.toCoords ∈ u.out_neighbors)
    (hd : v.dist = u.dist + 1)
    (h_anti : u.toCoords ∉ v.out_neighbors) :
    v.out_neighbors.toFinset
      ⊆ G.interiorNeighbors u v ∪ G.exteriorNeighbors u v := by
  have hc := cond_of_nodes hu_node hv_node hd
  intro x hx
  have hxv : x ∈ v.out_neighbors := List.mem_toFinset.mp hx
  by_cases hxu : x ∈ u.out_neighbors
  · apply Finset.mem_union_left
    rw [interiorNeighbors, if_pos hc]
    exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hxu, hx⟩
  · apply Finset.mem_union_right
    rw [exteriorNeighbors, if_pos hc]
    refine Finset.mem_inter.mpr ⟨?_, hx⟩
    rw [mem_getN2Finset_iff, getN1Finset_eq G hu u hu_node]
    refine ⟨⟨v.toCoords, List.mem_toFinset.mpr hadj, ?_⟩, ?_, ?_⟩
    · rw [getN1Finset_eq G hu v hv_node]; exact hx
    · intro h; exact h_anti (h ▸ hxv)
    · exact fun hmem => hxu (List.mem_toFinset.mp hmem)

theorem out_length_le_int_add_ext_general
    (G : GraphLevelOrder) (hu : G.CoordUnique)
    (u v : GLONode) (hu_node : u ∈ G.nodes) (hv_node : v ∈ G.nodes)
    (hadj : v.toCoords ∈ u.out_neighbors) (hd : v.dist = u.dist + 1)
    (h_anti : u.toCoords ∉ v.out_neighbors)
    (hnd : v.out_neighbors.Nodup) :
    v.out_neighbors.length
      ≤ (G.interiorNeighbors u v).card + (G.exteriorNeighbors u v).card := by
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card
    (out_subset_int_union_ext_general G hu u v hu_node hv_node hadj hd h_anti)).trans
    (Finset.card_union_le _ _)

theorem chain_ends_measure {α : Type*} (μ : α → Nat) (P Closes : α → Prop)
    (h0 : ∃ a, P a)
    (hstep : ∀ a, P a → Closes a ∨ ∃ b, P b ∧ μ b < μ a) :
    ∃ a, P a ∧ Closes a := by
  obtain ⟨a, ha, hmin⟩ :=
    (InvImage.wf μ wellFounded_lt).has_min {a | P a} h0
  rcases hstep a ha with hc | ⟨b, hb, hlt⟩
  · exact ⟨a, ha, hc⟩
  · exact absurd hlt (hmin b hb)

/-- Branch 1: no overlap between N⁺(b) and N⁺(a) makes `a` Seymour. -/
theorem seymour_of_disconnected_back_arc
    (G : GraphLevelOrder) (hu : G.CoordUnique)
    (a b : GLONode) (ha : a ∈ G.nodes) (hb : b ∈ G.nodes)
    (hback : b.toCoords ∈ a.out_neighbors)
    (h_anti : a.toCoords ∉ b.out_neighbors)
    (h_disc : ∀ z ∈ b.out_neighbors, z ∉ a.out_neighbors)
    (hbnd : b.out_neighbors.Nodup)
    (hreg : a.out_neighbors.length ≤ G.delta)
    (hmin : G.delta ≤ b.out_neighbors.length) :
    G.cardN1 a.toCoords ≤ G.cardN2 a.toCoords := by
  have h1 : G.cardN1 a.toCoords ≤ a.out_neighbors.length := by
    unfold cardN1
    rw [getN1Finset_eq G hu a ha]
    exact List.toFinset_card_le _
  have h2 : b.out_neighbors.length = b.out_neighbors.toFinset.card :=
    (List.toFinset_card_of_nodup hbnd).symm
  have h3 : b.out_neighbors.toFinset ⊆ getN2Finset G a.toCoords := by
    intro x hx
    have hxb := List.mem_toFinset.mp hx
    rw [mem_getN2Finset_iff, getN1Finset_eq G hu a ha]
    refine ⟨⟨b.toCoords, List.mem_toFinset.mpr hback, ?_⟩, ?_, ?_⟩
    · rw [getN1Finset_eq G hu b hb]; exact hx
    · intro h; exact h_anti (h ▸ hxb)
    · exact fun hmem => h_disc x hxb (List.mem_toFinset.mp hmem)
  have h4 := Finset.card_le_card h3
  unfold cardN2
  omega

/-- Disconnected back arcs cannot exist in a counterexample.
    `hpath` is branch 2, stated as a stake. -/
theorem no_disconnected_back_arc
    (G : GraphLevelOrder) (hu : G.CoordUnique)
    (hall : ∀ x ∈ G.nodes, ¬ (G.cardN1 x.toCoords ≤ G.cardN2 x.toCoords))
    (a b : GLONode) (ha : a ∈ G.nodes) (hb : b ∈ G.nodes)
    (hback : b.toCoords ∈ a.out_neighbors)
    (h_anti : a.toCoords ∉ b.out_neighbors)
    (hbnd : b.out_neighbors.Nodup)
    (hreg : a.out_neighbors.length ≤ G.delta)
    (hmin : G.delta ≤ b.out_neighbors.length)
    (hpath : (∃ z ∈ b.out_neighbors, z ∈ a.out_neighbors) →
        ∃ x ∈ G.nodes, G.cardN1 x.toCoords ≤ G.cardN2 x.toCoords) :
    False := by
  by_cases hint : ∃ z ∈ b.out_neighbors, z ∈ a.out_neighbors
  · obtain ⟨x, hx, hle⟩ := hpath hint
    exact hall x hx hle
  · push_neg at hint
    exact hall a ha
      (seymour_of_disconnected_back_arc G hu a b ha hb hback h_anti hint hbnd hreg hmin)

end GraphLevelOrder
