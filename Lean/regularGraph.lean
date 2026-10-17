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
    && u.out_neighbors.contains v.lexId && v.dist == u.dist + 1

def IsCounterexample (G : GraphLevelOrder) : Prop :=
  G.graph.IsOriented ∧
  G.graph.vertices.Nonempty ∧
  (∀ n ∈ G.nodes, n.out_neighbors.toFinset = G.graph.getN1Finset n.lexId) ∧
  ∀ x ∈ G.graph.vertices, G.graph.isNonSeymour x = true

/-- Total interior arcs: sum of |int(u,v)| over forward arcs u → v. -/
def interiorArcCount (G : GraphLevelOrder) : Nat :=
  G.nodes.foldl (fun acc u =>
    G.nodes.foldl (fun acc' v =>
      acc' + (if fwdArc G u v then (interiorNeighbors G u v).card else 0)) acc) 0

def IsMinimumCounterexample (G : GraphLevelOrder) : Prop :=
  IsCounterexample G ∧
  ∀ H : GraphLevelOrder, IsCounterexample H →
    interiorArcCount G ≤ interiorArcCount H


theorem lemma_rooted_neighborhood_size
    (g : GraphLevelOrder n) (delta : Nat) (h_delta : delta = g.minOutDegree)
    (h_dnsp : ∀ u ∈ g.nodes.toList, u.satisfiesDNSP g.adjacency_matrix) (i : Nat) :
    match i with
    | 0 => Fintype.card (g.rootedNeighborhood 0) = 1
    | 1 => Fintype.card (g.rootedNeighborhood 1) = delta
    | k + 2 => Fintype.card (g.rootedNeighborhood (k + 2)) ≤ delta - (k + 1) := by
  have h0 : Fintype.card (g.rootedNeighborhood 0) = 1 := by
    sorry  -- unique node at dist 0
  have h1 : Fintype.card (g.rootedNeighborhood 1) = delta := by
    sorry  -- root has out-degree minOutDegree; out-neighbors all lie in layer 1
  have hstep : ∀ j, 1 ≤ j →
      Fintype.card (g.rootedNeighborhood (j + 1))
        ≤ Fintype.card (g.rootedNeighborhood j) - 1 := by
    intro j hj
    exact h_dnsp_neighborhood_decrease g j h_dnsp  -- adjust to its real signature
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | k + 2 =>
    induction k with
    | zero =>
      have := hstep 1 le_rfl
      simp only [Nat.zero_add] at *   -- normalize 0+2 to 2 if needed
      omega                            -- |R2| ≤ |R1| - 1 = delta - 1
    | succ m ih =>
      have h := hstep (m + 2) (by omega)
      have e : m + 2 + 1 = m + 1 + 2 := rfl
      rw [e] at h
      omega                            -- |R_{m+3}| ≤ |R_{m+2}| - 1 ≤ delta - (m+2)
