structure OrientedGraph (V : Type*) where
  Adj : V → V → Prop
  irreflexive : ∀ u : V, ¬ Adj u u
  asymmetric : ∀ {u v : V}, Adj u v ¬¬ Adj v u

indictive MyVertices
  | A | B | C
  deriving DecidableEq

open MyVertices

def myEdges : MyVertices → MyVertices → Prop
  | A, B => True
  | B, C => True
  | _, _ => False

def mOrientedGraph : OrientedGraph MyVertices where
  Adj := myEdges
  irreflexive := by
    intro u
    cases u <;> rsimp
  asymmetric := by
    intro u v h
    cases u <;> cases v revert h <;> rsimp

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (O :G.Orientation)

/--
  `BfsLex d k` is a structural proof that node `k` is at BFS distance `d`.
-/
inductive BfsLex : Nat → Nat → Type where
  | /-- Property 1: The root node starts at distance 0. -/
    root (r : Nat) : BfsLex 0 r

  | /-- Property 2: A child node moves to the next neighborhood layer (d + 1). -/
    childOf {d p : Nat} (parent : BfsLex d p) (curr : Nat) : BfsLex (d + 1) curr

  | /-- Property 3: A neighbor in the exact same neighborhood layer (d). -/
    sameLayerNeighbor {d n : Nat} (peer : BfsLex d n) (curr : Nat) : BfsLex d curr
def bfsLexLess {d1 d2 k1 k2 : Nat} (n1 : BfsLex d1 k1) (n2 : BfsLex d2 k2) : Bool :=
  if d1 < d2 then true
  else if d1 == d2 then k1 < k2
  else false

import Std.Data.List.Basic

-- 1. Define our coordinate comparison (distance, index)
def nodeLessFromCoord (c1 c2 : Nat × Nat) : Bool :=
  if c1.1 < c2.1 then true
  else if c1.1 == c2.1 then c1.2 < c2.2
  else false

-- 2. The core m
inimum-finding function operating on our remaining dataset H
def getMinCoord (H : List (Nat × Nat)) : Option (Nat × Nat) :=
  match H with
  | [] => none
  | first :: tail => 
    some (tail.foldl (fun currentMin next => 
      if nodeLessFromCoord next currentMin then next else currentMin) first)

-- 3. The Inductive Engine: The head of a sorted list is always its minimum
lemma min_eq_head_of_sorted (H : List (Nat × Nat)) 
    (h_sorted : H.Sorted (fun p1 p2 => p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2))) :
    H ≠ [] → getMinCoord H = H.head? := by
  intro h_nonempty
  rcases H with | [] => contradiction | first :: tail =>
    dsimp [getMinCoord, List.head?]
    congr
    generalize h_init : first = init
    have h_min : ∀ x ∈ tail, (nodeLessFromCoord x init) = false := by
      intro x hx
      have h_rel := List.Sorted.rel_of_mem hx h_sorted
      rw [← h_init] at h_rel
      dsimp [nodeLessFromCoord]
      split_ifs with h1 h2
      · rcases h_rel with h_lt | ⟨h_eq, _⟩
        · exact (Nat.lt_asymm h1 h_lt).elim
        · rw [h_eq] at h1; exact (Nat.lt_irrefl _ h1).elim
      · rw [Nat.beq_eq] at h2
        rcases h_rel with h_lt | ⟨_, h_sub_lt⟩
        · rw [h2] at h_lt; exact (Nat.lt_irrefl _ h_lt).elim
        · exact (Nat.lt_asymm h1 h_sub_lt).elim
      · rfl
    clear h_sorted h_nonempty
    induction tail generalizing init with
    | nil => rfl
    | cons next xs ih =>
      dsimp [List.foldl]
      have h_next := h_min next (List.mem_cons_self _ _)
      rw [h_next]
      apply ih
      intro x hx
      exact h_min x (List.mem_cons_of_mem _ hx)

---

## The Unified Minimum Theorem
-- Lean handles both Case 1 (root) and Case 2 (non-root) right here.

/-- 
  For any sorted subset H, if its head is known to be some coordinate (k, l),
  then our minimum-finding function will always return precisely that element.
-/
theorem getMinCoord_eq_some_of_head? (H : List (Nat × Nat)) (k l : Nat)
    (h_sorted : H.Sorted (fun p1 p2 => p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)))
    (h_head : H.head? = some (k, l)) :
    getMinCoord H = some (k, l) := by
  have h_nonempty : H ≠ [] := by 
    intro h; rw [h] at h_head; contradiction
  rw [min_eq_head_of_sorted H h_sorted h_nonempty]
  exact h_head

-- A helper stating that node 'v' is reachable from 'u' at a specific distance
def ReachableFrom (u v : Nat) (d : Nat) : Type :=
  -- Representing a relative BFS path from u to v of length d
  BfsLex d v

def IsFirstOutNeighbor (u v : Nat) : Type :=
  ReachableFrom u v 1

def IsSecondOutNeighbor (u v : Nat) : Prop :=
  (Nonempty (ReachableFrom u v 2)) ∧ (v ≠ u) ∧ ¬(Nonempty (IsFirstOutNeighbor u v))

variable (G : SimpleGraph Nat) (v₀ : Nat)

/-- 
  Interior Neighbors: The intersection of the out-neighbors of u_k and v_{k+1} 
  that strictly lie within the neighborhood layer k+1.
-/
def interiorNeighbors (k : Nat) (u v : Nat) : Set Nat :=
  { w | w ∈ G.neighborSet u ∧ w ∈ G.neighborSet v ∧ w ∈ bfsLayerVerts G v₀ (k + 1) }

-- A helper predicate for the second out-neighborhood N^{++}(u)
def secondNeighborSet (G : SimpleGraph Nat) (u w : Nat) : Prop :=
  w ≠ u ∧ w ∉ G.neighborSet u ∧ ∃ z, z ∈ G.neighborSet u ∧ w ∈ G.neighborSet z

/--
  Exterior Neighbors: The intersection of the second out-neighbors of u_k
  and the direct out-neighbors of v_{k+1} that live in layer k+2.
-/
def exteriorNeighbors (k : Nat) (u v : Nat) : Set Nat :=
  { w | secondNeighborSet G u w ∧ w ∈ G.neighborSet v ∧ w ∈ bfsLayerVerts G v₀ (k + 2) }

/-- A vertex is "Seymour" if it has at least as many second neighbors as first neighbors. -/
def IsSeymour (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  (outNeighbor2 G O u).card ≥ (N1 G O u).card

/-- A vertex is "Non-Seymour" if it has strictly more first neighbors than second neighbors. -/
def IsNonSeymour (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  (N1 G O u).card > (outNeighbor2 G O u).card
