import SSNC.FiniteGraph
import Mathlib.Data.Finset.Max

namespace FiniteGraph
open scoped Classical

/-- Walk of exactly `n` edges from `u` to `v`. -/
inductive PathLen (G : FiniteGraph) : Nat → Nat → Nat → Prop
  | refl (u : Nat) : PathLen G u u 0
  | step {u v w n : Nat} : G.Adj u v → PathLen G v w n → PathLen G u w (n + 1)

/-- The shortest path length is the least `n` for which a path exists. -/
def ShortestPathLen (G : FiniteGraph) (u v n : Nat) : Prop :=
  PathLen G u v n ∧ ∀ m, PathLen G u v m → n ≤ m

noncomputable def getMinOutDegNode (G : FiniteGraph) : Nat :=
  match G.vertices.toList with
  | [] => 0
  | u :: us =>
    us.foldl (fun best u' =>
      if cardN1 G u' < cardN1 G best then u' else best
    ) u


lemma ShortestPathLen.unique (G : FiniteGraph) (u v n m : Nat)
    (h₁ : G.ShortestPathLen u v n) (h₂ : G.ShortestPathLen u v m) : n = m :=
  le_antisymm (h₁.2 m h₂.1) (h₂.2 n h₁.1)

/-- Spec: `u` is a vertex of minimum out-degree. -/
def IsMinOutDeg (G : FiniteGraph) (u : Nat) : Prop :=
  u ∈ G.vertices ∧ ∀ v ∈ G.vertices, G.cardN1 u ≤ G.cardN1 v

/-- Existence is a theorem, so no junk default like `0` is needed. -/
lemma exists_minOutDeg (G : FiniteGraph) (h : G.vertices.Nonempty) : ∃ u, G.IsMinOutDeg u := by
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image G.vertices G.cardN1 h
  exact ⟨u, hu, hmin⟩

noncomputable def minOutDegNode? (G : FiniteGraph) : Option Nat :=
  if h : G.vertices.Nonempty then
    some (Classical.choose (exists_minOutDeg G h))
  else none

/-- One BFS layer: unvisited out-neighbors of the frontier. -/
def bfsNext (G : FiniteGraph) (visited frontier : Finset Nat) : Finset Nat :=
  (frontier.biUnion G.N1) \ (visited ∪ frontier)

lemma mem_bfsNext (G : FiniteGraph) (visited frontier : Finset Nat) (v : Nat) :
    v ∈ G.bfsNext visited frontier ↔ (∃ u ∈ frontier, G.Adj u v) ∧ v ∉ visited ∧ v ∉ frontier := by
  simp [bfsNext, Finset.mem_biUnion, not_or]

/-- Distance to `t`, `none` if unreachable within the fuel. -/
def bfsDist (G : FiniteGraph) (t : Nat) :
    Nat → Nat → Finset Nat → Finset Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, d, visited, frontier =>
    if t ∈ frontier then some d
    else bfsDist G t fuel (d + 1) (visited ∪ frontier) (G.bfsNext visited frontier)

/-- Distance from `s` to `t`. `Option`, so unreachable is not confused with 0. -/
def getDist? (G : FiniteGraph) (s t : Nat) : Option Nat :=
  G.bfsDist t (G.vertices.card + 1) 0 ∅ {s}

/-- Common out-neighbors of `u` and `v`. -/
def interiorNbrs (G : FiniteGraph) (u v : Nat) : Finset Nat := G.N1 u ∩ G.N2 v

lemma mem_interiorNbrs (G : FiniteGraph) (u v w : Nat) :
    w ∈ G.interiorNbrs u v ↔
      G.Adj u w ∧ ((∃ x, G.Adj v x ∧ G.Adj x w) ∧ w ≠ v ∧ ¬ G.Adj v w) := by
  simp [interiorNbrs, mem_N2]

/-- Second out-neighbors of `u` that are out-neighbors of `v`. -/
def exteriorNbrs (G : FiniteGraph) (u v : Nat) : Finset Nat := G.N2 u ∩ G.N1 v

lemma mem_exteriorNbrs (G : FiniteGraph) (u v w : Nat) :
    w ∈ G.exteriorNbrs u v ↔
      ((∃ x, G.Adj u x ∧ G.Adj x w) ∧ w ≠ u ∧ ¬ G.Adj u w) ∧ G.Adj v w := by
  simp [exteriorNbrs, mem_N2]

lemma interiorNbrs_subset_vertices (G : FiniteGraph) (u v w : Nat) (h : w ∈ G.interiorNbrs u v) :
    w ∈ G.vertices := N1_subset_vertices (Finset.mem_inter.1 h).1

lemma interior_exterior_disjoint (G : FiniteGraph) (u v : Nat) :
    Disjoint (G.interiorNbrs u v) (G.exteriorNbrs u v) :=
  Finset.disjoint_left.2 fun w hi he =>
    (mem_N2.1 (Finset.mem_inter.1 he).1).2.2
      (mem_N1.1 (Finset.mem_inter.1 hi).1)

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

/-- The invariant, stated once. `size j` is the number of nodes in layer `j`. -/
structure ShrinkingProfile (size : Nat → Nat) (delta : Nat) : Prop where
  first : size 1 = delta
  step  : ∀ j, 1 ≤ j → size (j + 1) = size j - 1

namespace ShrinkingProfile
variable {size : Nat → Nat} {delta : Nat}

/-- Cleaner form: index `m + 1` instead of `m + 2`, so the base case is `first`. -/
theorem size_succ (h : ShrinkingProfile size delta) (m : Nat) :
    size (m + 1) = delta - m := by
  induction m with
  | zero => simpa using h.first
  | succ m ih =>
    rw [h.step (m + 1) (by omega), ih]
    omega

/-- Your original statement, now with no hypotheses beyond the bundled profile. -/
theorem size_add_two (h : ShrinkingProfile size delta) (m : Nat) :
    size (m + 2) = delta - (m + 1) :=
  h.size_succ (m + 1)

/-- Free consequence: layers are empty from index `delta + 1` on. -/
theorem size_eq_zero (h : ShrinkingProfile size delta) {j : Nat}
    (hj : delta < j) : size j = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [h.size_succ]; omega

end ShrinkingProfile

end FiniteGraph
