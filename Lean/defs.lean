structure OrientedGraph (V : Type*) where
  Adj : V → V → Prop
  irreflexive : ∀ u : V, 
