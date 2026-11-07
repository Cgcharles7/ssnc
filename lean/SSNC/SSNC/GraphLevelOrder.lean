import SSNC.FiniteGraph
import Mathlib.Data.List.Basic
import Mathlib.Order.Prod.Lex.Basic

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

def removeOut (n : GLONode) (c : Coord) : GLONode :=
  { n with out_neighbors := n.out_neighbors.filter (· ≠ c) }

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
  rw [h_cond]
  intro h
  simpa [Finset.mem_inter, List.mem_toFinset] using h


theorem exterior_neighbor_implies_second_neighbor
    (G : GraphLevelOrder) (u v : GLONode) (c : Coord)
    (h_cond : (G.nodes.contains u && G.nodes.contains v
               && v.dist == u.dist + 1) = true)
    (hc : c ∈ exteriorNeighbors G u v) :
    c ∈ getN2Finset G u.toCoords := by
  unfold exteriorNeighbors at hc
  rw [h_cond] at hc
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

def getLayerAtDistance (g : GraphLevelOrder) (k : Nat) : Finset (GLONode) :=
  -- Assuming g.nodes has a conversion to Finset or is a Finset/List
  (g.nodes.toList.filter (fun u => u.dist == k)).toFinset

/-- Neighborhood density at layer k, defined as the ratio of interior arcs to layer size. -/
def neighborhood_density (G : GraphLevelOrder) (k : Nat) : Rat :=
  let layerSize := (getLayerAtDistance G k).card
  let arcCount := layerInteriorArcCount G k
  if layerSize = 0 then 0
  else (arcCount : Rat) / (layerSize : Rat)

/-- Arcs u→c and v→c for each interior neighbour c of the forward pair (u,v). -/
def interiorArcs (G : GraphLevelOrder) (u v : GLONode) : Finset (Coord × Coord) :=
  if G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1 then
    (interiorNeighbors G u v).image (fun c => (u.toCoords, c)) ∪
    (interiorNeighbors G u v).image (fun c => (v.toCoords, c))
  else
    ∅

end GraphLevelOrder
