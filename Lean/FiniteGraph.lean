import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Basic

/-
-------------------------------------------------------------------------------
Stage 1: Finite Graph & Seymour Conjecture Primitives
-------------------------------------------------------------------------------
-/

structure FiniteGraph where
  vertices : Finset Nat
  edges : Finset (Nat Ã— Nat)
  edge_valid : âˆ€ e âˆˆ edges, e.1 âˆˆ vertices âˆ§ e.2 âˆˆ vertices

namespace FiniteGraph

/-- Adjacency predicate derived from the edge finset -/
def Adj (G : FiniteGraph) (u v : Nat) : Prop :=
  (u, v) âˆˆ G.edges

instance (G : FiniteGraph) (u v : Nat) : Decidable (G.Adj u v) :=
  Finset.decidableMem (u, v) G.edges

def getN1Finset (G : FiniteGraph) (u : Nat) : Finset Nat :=
  (G.edges.filter (fun e => e.1 = u)).image (fun e => e.2)

def cardN1 (G : FiniteGraph) (u : Nat) : Nat :=
  (getN1Finset G u).card

def getN2Finset (G : FiniteGraph) (u : Nat) : Finset Nat :=
  let n1 := getN1Finset G u
  let all_n2 := n1.biUnion (fun v => getN1Finset G v)
  all_n2.filter (fun w => w â‰  u âˆ§ w âˆ‰ n1)

def cardN2 (G : FiniteGraph) (u : Nat) : Nat :=
  (getN2Finset G u).card

def isSeymour (G : FiniteGraph) (u : Nat) : Bool :=
  cardN2 G u â‰¥ cardN1 G u

def isNonSeymour (G : FiniteGraph) (u : Nat) : Bool :=
  cardN2 G u < cardN1 G u

def IsIrreflexive (G : FiniteGraph) : Prop :=
  âˆ€ u âˆˆ G.vertices, Â¬ G.Adj u u

def IsAntisymmetric (G : FiniteGraph) : Prop :=
  âˆ€ u v, G.Adj u v â†’ G.Adj v u â†’ u = v

/-- An oriented graph is irreflexive and antisymmetric (no 2-cycles) -/
def IsOriented (G : FiniteGraph) : Prop :=
  G.IsIrreflexive âˆ§ G.IsAntisymmetric

def IsSeymourProp (G : FiniteGraph) (u : Nat) : Prop :=
  cardN1 G u â‰¤ cardN2 G u

lemma isSeymour_iff (G : FiniteGraph) (u : Nat) :
    G.isSeymour u = true â†” G.IsSeymourProp u := by
  dsimp [isSeymour, IsSeymourProp]
  rw [Bool.decide_iff]

end FiniteGraph
