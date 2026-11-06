import SSNC.Basic.GraphLevelOrder

namespace GraphLevelOrder   -- reopen it
/-- All interior arcs of G, over every forward pair. -/
def allInteriorArcs (G : GraphLevelOrder) : Finset (Coord × Coord) :=
  G.nodes.toList.toFinset.biUnion fun u =>
    G.nodes.toList.toFinset.biUnion fun v => interiorArcs G u v

def interiorOutDegree (G : GraphLevelOrder) (x : Coord) : Nat :=
  ((allInteriorArcs G).filter (fun a => a.1 = x)).card

def interiorInDegree (G : GraphLevelOrder) (x : Coord) : Nat :=
  ((allInteriorArcs G).filter (fun a => a.2 = x)).card

def totalInteriorDegree (G : GraphLevelOrder) (x : Coord) : Nat :=
  interiorInDegree G x + interiorOutDegree G x

def maxTotalInteriorDegree (G : GraphLevelOrder) : Nat :=
  G.nodes.toList.toFinset.sup fun w => totalInteriorDegree G w.toCoords

def interiorArcCount (G : GraphLevelOrder) : Nat := (allInteriorArcs G).card

def mceMetric (G : GraphLevelOrder) : Lex (Nat × Nat) :=
  toLex (interiorArcCount G, maxTotalInteriorDegree G)

def removeArc (G : GraphLevelOrder) (x c : Coord) : GraphLevelOrder :=
  { G with nodes := G.nodes.map fun n => if n.toCoords = x then n.removeOut c else n }

def IsMinimumCounterexample (G : GraphLevelOrder) : Prop :=
  IsCounterexample G ∧
  ∀ H, IsCounterexample H → mceMetric G ≤ mceMetric H

theorem mce_not_reducible {H : GraphLevelOrder}
    (hmce : IsMinimumCounterexample H) (G : GraphLevelOrder)
    (hG : IsCounterexample G) : ¬ mceMetric G < mceMetric H :=
  not_lt_of_ge (hmce.2 G hG)

theorem mceMetric_lt_of_arcCount_lt {G H : GraphLevelOrder}
    (h : interiorArcCount G < interiorArcCount H) :
    mceMetric G < mceMetric H := by
  unfold mceMetric
  rw [Prod.Lex.lt_iff]   -- name may differ by Mathlib version
  exact Or.inl h

theorem not_mce_of_removable
    {H : GraphLevelOrder} (x c : Coord)
    (hlt  : interiorArcCount (H.removeArc x c) < interiorArcCount H)
    (hcex : IsCounterexample (H.removeArc x c)) :
    ¬ IsMinimumCounterexample H := by
  intro hmce
  exact mce_not_reducible hmce _ hcex (mceMetric_lt_of_arcCount_lt hlt)

end GraphLevelOrder
