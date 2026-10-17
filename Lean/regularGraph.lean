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

def ConnectedBack (G : GraphLevelOrder) (u v : GLONode) : Prop :=
  ∃ x ∈ backL G v, x ∈ u.out_neighbors

def NoConnectedBack (G : GraphLevelOrder) : Prop :=
  ∀ u v, fwdArc G u v = true → ¬ ConnectedBack G u v
    interiorArcCount G ≤ interiorArcCount H


theorem lemma_6_9_under_no_back_arcs
    (g : GraphLevelOrder n) 
    (delta : Nat) 
    (h_delta : delta = g.minOutDegree)
    -- Hypothesis 1: Every node in the MCE is non-Seymour
    (h_all_non_seymour : ∀ u ∈ g.nodes.toList, u.isSeymourNode g.adjacency_matrix = false)
    -- Hypothesis 2: No back arcs exist (out-neighbors only go forward or strictly layer-by-layer)
    (h_no_back_arcs : ∀ u ∈ g.nodes.toList, ∀ v_id ∈ getOutNeighbors g u, 
      match g.findNode? v_id with
      | some v => v.dist ≥ u.dist
      | none => True)
    (i : Nat) :
    match i with
    | 0 => Fintype.card (g.rootedNeighborhood 0) = 1
    | 1 => Fintype.card (g.rootedNeighborhood 1) = delta
    | k + 2 => Fintype.card (g.rootedNeighborhood (k + 2)) ≤ delta - (k + 1) := by
  
  -- Base Case 0: The root layer contains only the root node v0, so its card is 1
  have h0 : Fintype.card (g.rootedNeighborhood 0) = 1 := by
    -- Unfold g.rootedNeighborhood 0 or apply your singleton root property
    -- If defined as {g.root}:
    exact Finset.card_singleton g.root
    -- (Or use `rfl` / `simp` depending on your exact rooted definition)

  -- Base Case 1: Layer 1 consists of the root's out-neighbors, whose count equals delta
  have h1 : Fintype.card (g.rootedNeighborhood 1) = delta := by
    rw [h_delta]
    -- Since layer 1 is defined as outNeighbors of the root, 
    -- and the root's out-degree is defined as minOutDegree:
    exact g.root_out_degree_eq_min

  -- Inductive step: No back arcs + non-Seymour forces strict linear decrease
  have h_step : ∀ j, 1 ≤ j →
      Fintype.card (g.rootedNeighborhood (j + 1))
        ≤ Fintype.card (g.rootedNeighborhood j) - 1 := by
    intro j hj
    -- Because there are no back arcs and every node is non-Seymour, 
    -- neighborhood cardinality strictly drops at each layer transition.
    exact neighborhood_decrease_of_no_back_arcs g j h_all_non_seymour h_no_back_arcs

  match i with
  | 0 => exact h0
  | 1 => exact h1
  | k + 2 =>
    induction k with
    | zero =>
      have := h_step 1 le_rfl
      simp only [Nat.zero_add] at *
      omega
    | succ m ih =>
      have h := h_step (m + 2) (by omega)
      have e : m + 2 + 1 = m + 1 + 2 := rfl
      rw [e] at h
      omega

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

theorem extL_subset_layer (G : GraphLevelOrder n) (v : GLONode n) :
    extL G v ⊆ layerIds G (v.dist + 1) := by
  intro x hx
  -- 1. Unfold membership in extL
  -- Typically, extL filters out-neighbors of v where the distance equals v.dist + 1
  simp only [extL, Finset.mem_filter, List.mem_toFinset] at hx
  rcases hx with ⟨h_in_nbrs, h_dist_eq⟩
  
  -- 2. Unfold membership in layerIds (nodes in graph with dist = v.dist + 1)
  simp only [layerIds, Finset.mem_filter]
  constructor
  · -- Prove x belongs to the underlying node collection / finset of the graph
    -- Usually derived from h_in_nbrs since an out-neighbor must be a valid node in G
    exact out_neighbor_node_exists_in_graph G v x h_in_nbrs
  · -- Prove x's distance matches v.dist + 1
    exact h_dist_eq

/-- Degree partition with no back arcs (Lemma 3.1, layer form). -/
theorem out_card_split (G : GraphLevelOrder) (v : GLONode)
    (hnd : v.out_neighbors.Nodup)
    (hbfs : ∀ x ∈ v.out_neighbors, ∃ d, G.distOf x = some d ∧ d ≤ v.dist + 1)
    (hnb : backL G v = ∅) :
    v.out_neighbors.length = (intL G v).card + (extL G v).card := by
  -- 1. List length equals finset cardinality due to Nodup
  rw [Finset.card_list_toFinset _ hnd]
  
  -- 2. Prove that the out-neighbor finset splits exactly into intL and extL
  have h_union : v.out_neighbors.toFinset = intL G v ∪ extL G v := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_union, mem_intL, mem_extL]
    constructor
    · intro hx
      rcases hbfs x hx with ⟨d, hd_some, hd_le⟩
      -- Because backL G v = ∅, x cannot be a back-arc. 
      -- Thus its distance is either v.dist (interior) or v.dist + 1 (exterior).
      have h_not_back : ¬ (d < v.dist) := by
        intro h_back
        -- If d < v.dist, x would belong to backL G v, contradicting hnb = ∅
        have : x ∈ backL G v := by 
          -- unfolding backL membership using hd_some and h_back
          sorry 
        rw [hnb] at this
        exact Finset.not_mem_empty x this
      omega
    · intro h
      rcases h with h_int | h_ext
      · -- If in intL, it's an out-neighbor by definition of intL subset out_neighbors
        exact mem_out_neighbors_of_intL G v x h_int
      · -- If in extL, it's an out-neighbor by definition of extL subset out_neighbors
        exact mem_out_neighbors_of_extL G v x h_ext

  rw [h_union]

  -- 3. Apply card_union_of_disjoint since internal and exterior occupy distinct layers
  apply Finset.card_union_of_disjoint
  intro x hxi hxe
  simp only [mem_intL, mem_extL] at hxi hxe
  -- Distance contradictions (d = v.dist vs d = v.dist + 1) resolved by omega
  omega

/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/
theorem irregularity_extra_exterior_contradiction (G : GraphLevelOrder) (δ k : Nat) (hC : IsCounterexample G)
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

theorem interior_lower_bound (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hback : backC = 0)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    k + 1 ≤ intC := by omega


/-- Back arcs forced by interior deficiency (no load balance, no minimality). -/
theorem back_ge_deficiency (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    (k + 1) - intC ≤ backC := by omega

theorem lemmaA_core (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ)
    (hdef : intC < k + 1) : 0 < backC := by omega

theorem layers_disjoint
    (k1 k2 : Nat) (v_k1 v_k2 : GLONode)
    (h_dist1 : v_k1.dist = k1) (h_dist2 : v_k2.dist = k2)
    (h_neq : k1 ≠ k2) : v_k1 ≠ v_k2 := by
  intro h_eq
  apply h_neq
  rw [← h_dist1, ← h_dist2, h_eq]

/-- Node-level consistency: out-neighbors split into back / interior / exterior. -/
def PartitionWF (n : GLONode) : Prop :=
  n.out_neighbors.length =
    n.back_neighbors.length + n.interior_neighbors.length + n.exterior_neighbors.length

lemma child_interior_deficit
    (child : GLONode) (k : Nat)
    (h_part : PartitionWF child)
    (h_deg : k ≤ child.out_neighbors.length)
    (h_int : child.interior_neighbors.length < k) :
    0 < child.back_neighbors.length ∨ 0 < child.exterior_neighbors.length := by
  unfold PartitionWF at h_part
  omega

/-- Pigeonhole: an irregular child cannot fit its exterior in one layer. -/
theorem extra_forward_arc_makes_seymour (G : GraphLevelOrder) (δ k : Nat) (v : GLONode)
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


theorem interior_lower_bound (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hback : backC = 0)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    k + 1 ≤ intC := by omega
