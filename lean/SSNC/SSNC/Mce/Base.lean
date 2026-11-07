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

end GraphLevelOrder
