import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

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

def N1 (G : FiniteGraph) (u : Nat) : Finset Nat :=
  (G.edges.filter (fun e => e.1 = u)).image (fun e => e.2)

def N2 (G : FiniteGraph) (u : Nat) : Finset Nat :=
  ((G.N1 u).biUnion G.N1).filter (fun w => w ≠ u ∧ w ∉ G.N1 u)

def cardN1 (G : FiniteGraph) (u : Nat) : Nat := (G.N1 u).card
def cardN2 (G : FiniteGraph) (u : Nat) : Nat := (G.N2 u).card

def getN1Finset (G : FiniteGraph) (u : Nat) : Finset Nat :=
  (G.edges.filter (fun e => e.1 = u)).image (fun e => e.2)

def getN2Finset (G : FiniteGraph) (u : Nat) : Finset Nat :=
  let n1 := getN1Finset G u
  let all_n2 := n1.biUnion (fun v => getN1Finset G v)
  all_n2.filter (fun w => w ≠ u ∧ w ∉ n1)

def isSeymour (G : FiniteGraph) (u : Nat) : Bool := cardN2 G u ≥ cardN1 G u

def IsSeymour  (G : FiniteGraph) (u : Nat) : Prop := G.cardN1 u ≤ G.cardN2 u

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

@[simp] lemma mem_N1 {G : FiniteGraph} {u v : Nat} :
    v ∈ G.N1 u ↔ G.Adj u v := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, he, hb⟩ := Finset.mem_image.1 h
    obtain ⟨he', ha⟩ := Finset.mem_filter.1 he
    simp only at ha hb
    subst ha; subst hb
    exact he'
  · intro h
    exact Finset.mem_image.2 ⟨(u, v), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

lemma mem_N2 {G : FiniteGraph} {u w : Nat} :
    w ∈ G.N2 u ↔ (∃ v, G.Adj u v ∧ G.Adj v w) ∧ w ≠ u ∧ ¬ G.Adj u w := by
  simp [N2, Finset.mem_biUnion, mem_N1]

lemma Adj.mem_vertices {G : FiniteGraph} {u v : Nat} (h : G.Adj u v) :
    u ∈ G.vertices ∧ v ∈ G.vertices :=
  G.edge_valid (u, v) h

lemma N1_subset_vertices {G : FiniteGraph} {u w : Nat} (h : w ∈ G.N1 u) :
    w ∈ G.vertices := (mem_N1.1 h).mem_vertices.2

lemma N2_subset_vertices {G : FiniteGraph} {u w : Nat} (h : w ∈ G.N2 u) :
    w ∈ G.vertices := by
  obtain ⟨⟨v, _, hvw⟩, -, -⟩ := mem_N2.1 h
  exact hvw.mem_vertices.2

lemma disjoint_N1_N2 (G : FiniteGraph) (u : Nat) : Disjoint (G.N1 u) (G.N2 u) :=
  Finset.disjoint_left.2 fun _ h1 h2 => (mem_N2.1 h2).2.2 (mem_N1.1 h1)

lemma N2_not_mem_self {G : FiniteGraph} {u : Nat} : u ∉ G.N2 u := fun h =>
  (mem_N2.1 h).2.1 rfl

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
