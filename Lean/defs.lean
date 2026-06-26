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
