import SSNC.Mce.Base
import Mathlib.Data.Finset.Lattice.Fold   -- for Finset.sup

namespace GraphLevelOrder

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
