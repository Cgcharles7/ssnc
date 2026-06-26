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
