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

/-- Total interior arcs: sum of |int(u,v)| over forward arcs u → v. -/
def interiorArcCount (G : GraphLevelOrder) : Nat :=
  G.nodes.foldl (fun acc u =>
    G.nodes.foldl (fun acc' v =>
      acc' + (if fwdArc G u v then (G.interiorNeighbors u v).card else 0)) acc) 0

def IsMinimumCounterexample (G : GraphLevelOrder) : Prop :=
  IsCounterexample G ∧
  ∀ H : GraphLevelOrder, IsCounterexample H →
    interiorArcCount G ≤ interiorArcCount H

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

def getLayerAtDistance (g : GraphLevelOrder) (k : Nat) : Finset (GLONode) :=
  -- Assuming g.nodes has a conversion to Finset or is a Finset/List
  (g.nodes.toList.filter (fun u => u.dist == k)).toFinset

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
    (g : GraphLevelOrder) (delta : Nat) (h_delta : delta = g.delta)
    (h_all_non_seymour : ∀ u ∈ g.nodes.toList, g.isNonSeymour (u.dist, u.lexId) = true)
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


namespace GraphLevelOrder

/-- Layer-based sets for a node v (ids of out-neighbors by layer). -/
def intNbrs (v : GLONode) : Finset Coord :=
  v.out_neighbors.toFinset.filter (·.1 = v.dist)

def extNbrs (v : GLONode) : Finset Coord :=
  v.out_neighbors.toFinset.filter (·.1 = v.dist + 1)

def backNbrs (v : GLONode) : Finset Coord :=
  v.out_neighbors.toFinset.filter (·.1 < v.dist)

def layerIds (G : GraphLevelOrder) (j : Nat) : Finset Nat :=
  ((G.nodes.filter (·.dist == j)).toList.map (·.lexId)).toFinset

def layerCoords (G : GraphLevelOrder) (j : Nat) : Finset Coord :=
  ((G.nodes.toList.filter (·.dist == j)).map (·.toCoords)).toFinset

def BFSWF (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, ∀ x ∈ v.out_neighbors,
    (∃ d ∈ G.nodes, d.toCoords = x) ∧ x.1 ≤ v.dist + 1

theorem extNbrs_subset_layer (G : GraphLevelOrder) (hw : G.BFSWF)
    (v : GLONode) (hv : v ∈ G.nodes) :
    extNbrs v ⊆ layerCoords G (v.dist + 1) := by
  intro x hx
  -- x is an out-neighbor of v whose layer is v.dist + 1
  simp only [extNbrs, Finset.mem_filter, List.mem_toFinset] at hx
  obtain ⟨hin, hlayer⟩ := hx
  -- BFSWF: x is the coordinate of some real node d of G
  obtain ⟨⟨d, hd_mem, hd_eq⟩, _⟩ := hw v hv x hin
  have hdd : d.dist = x.1 := by rw [← hd_eq]; rfl
  -- membership in layerCoords: x = d.toCoords for some d in layer v.dist + 1
  simp only [G.layerCoords, List.mem_toFinset, List.mem_map, List.mem_filter,
    Array.mem_toList, beq_iff_eq]
  exact ⟨d, ⟨hd_mem, by omega⟩, hd_eq⟩

/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/

def IsMinOutDeg (G : GraphLevelOrder) (δ : Nat) : Prop :=
  (∀ x ∈ G.graph.vertices, δ ≤ G.graph.cardN1 x) ∧
  (∃ x ∈ G.graph.vertices, G.graph.cardN1 x = δ)

def NoBackArcs (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, backNbrs v = ∅

theorem irregularity_extra_exterior_contradiction
    (G : GraphLevelOrder) (k : Nat)
    (hC : IsCounterexample G)
    (hmin : IsMinOutDeg G G.delta)
    (hw : G.BFSWF)
    (hnb : NoBackArcs G)
    (u v : GLONode)
    (hfwd : fwdArc G u v = true)
    (hu : u.dist = k) (hudeg : u.out_neighbors.length = G.delta)
    (hnd : v.out_neighbors.Nodup)
    (hirr : G.delta < v.out_neighbors.length)
    (hk : k + 1 ≤ G.delta) : False := by
  obtain ⟨_, hv_node, _, hdist'⟩ := (fwdArc_spec G u v).mp hfwd
  have hdist : v.dist = k + 1 := by omega
  have hint := interior_bound_of_nonSeymour G k hC hmin hnb u v hfwd hu hudeg
  have hcor : (layerCoords G (v.dist + 1)).card ≤ G.delta - (k + 1) := by
    rw [hdist]; exact cor_3_10 G hC hmin k
  have hsplit := out_card_split v hnd
    (fun x hx => (hw v hv_node x hx).2) (hnb v hv_node)
  have hsub := Finset.card_le_card (extNbrs_subset_layer G hw v hv_node)
  omega

end GraphLevelOrder

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

theorem lemmaA_core (δ k intC extC backC outC : Nat)
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

---
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

/-- Total interior arcs: sum of |int(u,v)| over forward arcs u → v. -/
def interiorArcCount (G : GraphLevelOrder) : Nat :=
  G.nodes.foldl (fun acc u =>
    G.nodes.foldl (fun acc' v =>
      acc' + (if fwdArc G u v then (G.interiorNeighbors u v).card else 0)) acc) 0

def IsMinimumCounterexample (G : GraphLevelOrder) : Prop :=
  IsCounterexample G ∧
  ∀ H : GraphLevelOrder, IsCounterexample H →
    interiorArcCount G ≤ interiorArcCount H

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

def getLayerAtDistance (g : GraphLevelOrder) (k : Nat) : Finset (GLONode) :=
  -- Assuming g.nodes has a conversion to Finset or is a Finset/List
  (g.nodes.toList.filter (fun u => u.dist == k)).toFinset

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
    (g : GraphLevelOrder) (delta : Nat) (h_delta : delta = g.delta)
    (h_all_non_seymour : ∀ u ∈ g.nodes.toList, g.isNonSeymour (u.dist, u.lexId) = true)
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


namespace GraphLevelOrder

/-- Layer-based sets for a node v (ids of out-neighbors by layer). -/
def intNbrs (v : GLONode) : Finset Coord :=
  v.out_neighbors.toFinset.filter (·.1 = v.dist)

def extNbrs (v : GLONode) : Finset Coord :=
  v.out_neighbors.toFinset.filter (·.1 = v.dist + 1)

def backNbrs (v : GLONode) : Finset Coord :=
  v.out_neighbors.toFinset.filter (·.1 < v.dist)

def layerIds (G : GraphLevelOrder) (j : Nat) : Finset Nat :=
  ((G.nodes.filter (·.dist == j)).toList.map (·.lexId)).toFinset

def layerCoords (G : GraphLevelOrder) (j : Nat) : Finset Coord :=
  ((G.nodes.toList.filter (·.dist == j)).map (·.toCoords)).toFinset

def BFSWF (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, ∀ x ∈ v.out_neighbors,
    (∃ d ∈ G.nodes, d.toCoords = x) ∧ x.1 ≤ v.dist + 1

theorem extNbrs_subset_layer (G : GraphLevelOrder) (hw : G.BFSWF)
    (v : GLONode) (hv : v ∈ G.nodes) :
    extNbrs v ⊆ layerCoords G (v.dist + 1) := by
  intro x hx
  -- x is an out-neighbor of v whose layer is v.dist + 1
  simp only [extNbrs, Finset.mem_filter, List.mem_toFinset] at hx
  obtain ⟨hin, hlayer⟩ := hx
  -- BFSWF: x is the coordinate of some real node d of G
  obtain ⟨⟨d, hd_mem, hd_eq⟩, _⟩ := hw v hv x hin
  have hdd : d.dist = x.1 := by rw [← hd_eq]; rfl
  -- membership in layerCoords: x = d.toCoords for some d in layer v.dist + 1
  simp only [G.layerCoords, List.mem_toFinset, List.mem_map, List.mem_filter,
    Array.mem_toList, beq_iff_eq]
  exact ⟨d, ⟨hd_mem, by omega⟩, hd_eq⟩

/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/

def IsMinOutDeg (G : GraphLevelOrder) (δ : Nat) : Prop :=
  (∀ x ∈ G.graph.vertices, δ ≤ G.graph.cardN1 x) ∧
  (∃ x ∈ G.graph.vertices, G.graph.cardN1 x = δ)

def NoBackArcs (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, backNbrs v = ∅

theorem irregularity_extra_exterior_contradiction
    (G : GraphLevelOrder) (k : Nat)
    (hC : IsCounterexample G)
    (hmin : IsMinOutDeg G G.delta)
    (hw : G.BFSWF)
    (hnb : NoBackArcs G)
    (u v : GLONode)
    (hfwd : fwdArc G u v = true)
    (hu : u.dist = k) (hudeg : u.out_neighbors.length = G.delta)
    (hnd : v.out_neighbors.Nodup)
    (hirr : G.delta < v.out_neighbors.length)
    (hk : k + 1 ≤ G.delta) : False := by
  obtain ⟨_, hv_node, _, hdist'⟩ := (fwdArc_spec G u v).mp hfwd
  have hdist : v.dist = k + 1 := by omega
  have hint := interior_bound_of_nonSeymour G k hC hmin hnb u v hfwd hu hudeg
  have hcor : (layerCoords G (v.dist + 1)).card ≤ G.delta - (k + 1) := by
    rw [hdist]; exact cor_3_10 G hC hmin k
  have hsplit := out_card_split v hnd
    (fun x hx => (hw v hv_node x hx).2) (hnb v hv_node)
  have hsub := Finset.card_le_card (extNbrs_subset_layer G hw v hv_node)
  omega

end GraphLevelOrder

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

theorem lemmaA_core (δ k intC extC backC outC : Nat)
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

theorem extra_forward_arc_contradiction
    (G : GraphLevelOrder) (hw : G.BFSWF) (k : Nat) (u v : GLONode)
    (hfwd : fwdArc G u v = true) (hv : v ∈ G.nodes)
    (hk : v.dist = k + 1)
    (hdeg : G.delta < v.out_neighbors.length)
    (hnd : v.out_neighbors.Nodup)
    (hnb : G.backNeighbors u v = ∅)
    (hno_same : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors)
    (hint : (G.interiorNeighbors u v).card ≤ k + 1)   -- to be derived
    (hlay : (G.layerCoords (k + 2)).card ≤ G.delta - (k + 1))
    (hk' : k + 1 ≤ G.delta) : False := by
  have hpart : v.out_neighbors.toFinset
      = G.interiorNeighbors u v ∪ G.exteriorNeighbors u v := sorry  -- out_sub_int_ext + reverse
  have hdis : Disjoint (G.interiorNeighbors u v) (G.exteriorNeighbors u v) :=
    int_ext_disjoint G u v hfwd
  have h2 : v.out_neighbors.length
      = (G.interiorNeighbors u v).card + (G.exteriorNeighbors u v).card := by
    rw [← List.toFinset_card_of_nodup hnd, hpart, Finset.card_union_of_disjoint hdis]
  have h1 := Finset.card_le_card
    ((extNeighbors_subset_extNbrs G u v hfwd hnb hno_same).trans
      (extNbrs_subset_layer G hw v hv))
  rw [hk] at h1
  omega

/-- Pigeonhole: an irregular child cannot fit its exterior in one layer. -/
theorem extra_forward_arc_makes_seymour (G : GraphLevelOrder) (k : Nat) (u v : GLONode)
    (hk : v.dist = k + 1)
    (hdeg : G.delta < v.out_neighbors.length) (hnd : v.out_neighbors.Nodup)
    (hint : (G.interiorNeighbors u v).card = k + 1) -- MCE Assumption
    (hpart : (v.out_neighbors.toFinset).card = (G.interiorNeighbors u v).card ∨ (G.exteriorNeighbors u v).card
    (hdis : Disjoint (intL G v) (extL G v))
    (hlay : (layerIds G (k + 2)).card ≤ G.delta - (k + 1)) : False := by
  have h1 := Finset.card_le_card (extL_subset_layer G v)
  rw [hk] at h1
  have h2 : v.out_neighbors.length = (intL G v).card + (extL G v).card := by
    rw [← List.toFinset_card_of_nodup hnd, hpart, Finset.card_union_of_disjoint hdis]
  omega

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
