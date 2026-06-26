structure OrientedGraph (V : Type*) where
  Adj : V → V → Prop
  irreflexive : ∀ u : V, ¬ Adj u u
  asymmetric : ∀ {u v : V}, Adj u v ¬¬ Adj v u
