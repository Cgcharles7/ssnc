import SSNC.FiniteGraph

/-- BFS-Lex coordinates -/
inductive GloLex (G : FiniteGraph) (delta : Nat) : (d : Nat) → (v : Nat) → Type where
  | root (r : Nat) (h_vert : r ∈ G.vertices) : GloLex G delta 0 r
  | childOf {d parent curr : Nat}
      (p : GloLex G delta d parent)
      (h_adj : G.Adj parent curr) : GloLex G delta (d + 1) curr
  | sameLayerNeighbor {d peer curr : Nat}
      (p : GloLex G delta d peer)
      (h_adj : G.Adj peer curr) : GloLex G delta d curr

namespace GloLex

variable {G : FiniteGraph} {delta : Nat}

def pathLength {d v : Nat} : GloLex G delta d v → Nat
  | root _ _ => 0
  | childOf p _ => pathLength p + 1
  | sameLayerNeighbor p _ => pathLength p

def toVertex {d v : Nat} (_ : GloLex G delta d v) : Nat := v

def toDist {d v : Nat} (_ : GloLex G delta d v) : Nat := d

end GloLex
