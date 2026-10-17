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

/-- Pigeonhole: an irregular child cannot fit its exterior in one layer. -/
theorem irregular_child_false (G : GraphLevelOrder) (δ k : Nat) (v : GLONode)
    (hk : v.dist = k + 1)
    (hdeg : δ < v.out_neighbors.length) (hnd : v.out_neighbors.Nodup)
    (hint : (intL G v).card = k + 1)          -- load balance
    (hpart : v.out_neighbors.toFinset = intL G v ∪ extL G v)
    (hdis : Disjoint (intL G v) (extL G v))
    (hlay : (layerIds G (k + 2)).card ≤ δ - (k + 1)) : False := by
  have h1 := Finset.card_le_card (extL_subset_layer G v)
  rw [hk] at h1
  have h2 : v.out_neighbors.length = (intL G v).card + (extL G v).card := by
    rw [← List.toFinset_card_of_nodup hnd, hpart, Finset.card_union_of_disjoint hdis]
  omega
      omega                            -- |R_{m+3}| ≤ |R_{m+2}| - 1 ≤ delta - (m+2)


namespace GraphLevelOrder

/-- Layer-based sets for a node v (ids of out-neighbors by layer). -/
def intL (G : GraphLevelOrder) (v : GLONode) : Finset Nat :=
  v.out_neighbors.toFinset.filter (fun x => G.distOf x == some v.dist)

def extL (G : GraphLevelOrder) (v : GLONode) : Finset Nat :=
  v.out_neighbors.toFinset.filter (fun x => G.distOf x == some (v.dist + 1))

def backL (G : GraphLevelOrder) (v : GLONode) : Finset Nat :=
  v.out_neighbors.toFinset.filter (fun x => (G.distOf x).any (· < v.dist))

def layerIds (G : GraphLevelOrder) (j : Nat) : Finset Nat :=
  ((G.nodes.filter (·.dist == j)).toList.map (·.lexId)).toFinset

/-- ext(v) lives inside the next layer. -/
theorem extL_subset_layer (G : GraphLevelOrder) (v : GLONode) :
    extL G v ⊆ layerIds G (v.dist + 1) := by
  sorry  -- distOf x = some d → ∃ node n, n.lexId = x ∧ n.dist = d

/-- Degree partition with no back arcs (Lemma 3.1, layer form). -/
theorem out_card_split (G : GraphLevelOrder) (v : GLONode)
    (hnd : v.out_neighbors.Nodup)
    (hbfs : ∀ x ∈ v.out_neighbors, ∃ d, G.distOf x = some d ∧ d ≤ v.dist + 1)
    (hnb : backL G v = ∅) :
    v.out_neighbors.length = (intL G v).card + (extL G v).card := by
  sorry  -- toFinset = intL ∪ extL, disjoint by distOf; then card_union_of_disjoint

/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/
theorem case1 (G : GraphLevelOrder) (δ k : Nat) (hC : IsCounterexample G)
    (hmin : IsMinOutDeg G δ) (hnb : NoBackArcs G)
    (u v : GLONode) (hfwd : fwdArc G u v = true)
    (hu : u.dist = k) (hudeg : u.out_neighbors.length = δ)
    (hnd : v.out_neighbors.Nodup)
    (hbfs : ∀ x ∈ v.out_neighbors, ∃ d, G.distOf x = some d ∧ d ≤ v.dist + 1)
    (hirr : δ < v.out_neighbors.length) (hk : k + 1 ≤ δ) : False := by
  have hint := interior_bound_of_nonSeymour G δ k hC hmin hnb u v hfwd hu hudeg
  have hcor := cor_3_10 G δ hC hmin k
  have hsplit := out_card_split G v hnd hbfs (by sorry)
  have hdist : v.dist = k + 1 := by
    simp [fwdArc] at hfwd; omega
  have hsub := Finset.card_le_card (extL_subset_layer G v)
  rw [hdist] at hsub
  omega
