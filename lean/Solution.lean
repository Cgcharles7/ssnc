import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic

structure FiniteGraph where
  vertices : Finset Nat
  edges : Finset (Nat × Nat)
  edge_valid : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices

namespace FiniteGraph
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

structure GraphLevelOrder where
  nodes            : Array GLONode
  delta            : Nat
  max_layer        : Nat
  graph            : FiniteGraph
  deriving Inhabited

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

def interiorNeighbors (G : GraphLevelOrder) (u v : GLONode) : Finset Coord :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    u.out_neighbors.toFinset ∩ v.out_neighbors.toFinset
  else
    ∅

def BFSWF (G : GraphLevelOrder) : Prop :=
  ∀ v ∈ G.nodes, ∀ x ∈ v.out_neighbors,
    (∃ d ∈ G.nodes, d.toCoords = x) ∧ x.1 ≤ v.dist + 1


end GraphLevelOrder

def fwdArc (G : GraphLevelOrder) (u v : GLONode) : Bool :=
  G.nodes.contains u && G.nodes.contains v
    && u.out_neighbors.contains v.toCoords && v.dist == u.dist + 1

def IsCounterexample (G : GraphLevelOrder) : Prop :=
  G.CoordUnique ∧
  G.IsOriented ∧
  0 < G.nodes.size ∧
  ∀ x ∈ G.nodes, G.isNonSeymour (x.dist, x.lexId) = true


def interiorArcCount (G : GraphLevelOrder) : Nat :=
  G.nodes.foldl (fun acc u =>
    G.nodes.foldl (fun acc' v =>
      acc' + (if fwdArc G u v then (G.interiorNeighbors u v).card else 0)) acc) 0

/-- NEW. Well-formedness of the layered representation: out-neighbors are nodes
    in the same or the next layer (`BFSWF`), every node has out-degree at least
    `delta`, and some root in layer 0 has out-degree exactly `delta`. -/
def IsLayered (G : GraphLevelOrder) : Prop :=
  G.BFSWF ∧
  (∀ x ∈ G.nodes, G.delta ≤ x.out_neighbors.length) ∧
  (∃ r ∈ G.nodes, r.dist = 0 ∧ r.out_neighbors.length = G.delta)

/-- NEW. A counterexample of minimum `interiorArcCount` among *layered*
    counterexamples. (Minimising over all counterexamples would let degenerate,
    non-layered ones force the count to 0.) -/
def IsMinimumLayeredCounterexample (G : GraphLevelOrder) : Prop :=
  IsLayered G ∧ IsCounterexample G ∧
  ∀ H : GraphLevelOrder, IsLayered H → IsCounterexample H →
    interiorArcCount G ≤ interiorArcCount H

/-! ======================================================================
    PASTE HERE: every lemma and theorem from your development
    (everything after the definitions above, without repeating them).
    ====================================================================== -/

theorem no_minimum_layered_counterexample
    (G : GraphLevelOrder) (hG : IsMinimumLayeredCounterexample G)
    (h3 : 3 ≤ G.delta) : False := by
  sorry  -- replace with your proof
