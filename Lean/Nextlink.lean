lemma lower_layer_neighbors_disjoint (i k : ℕ) (hk : k < i) (u_i v_k : V)
    (hu : u_i ∈ bfsLayerVerts G v₀ i)
    (hv : v_k ∈ bfsLayerVerts G v₀ k) :
    Disjoint (outNeighborsOld G O u_i) (N1 G O v_k) := by
  rw [Finset.disjoint_iff_forall_not_mem]
  intro w hw
  rcases hw with ⟨h_old, h_vk_out⟩
  
  -- Extract distance constraints from the layers
  simp [bfsLayerVerts] at hu hv
  simp [outNeighborsOld] at h_old -- Gives: G.dist v₀ w ≥ i
  
  -- Extract triangle inequality from v_k → w
  rw [N1, Finset.mem_filter] at h_vk_out
  have h_adj : G.Adj v_k w := h_vk_out.1
  have h_metric := G.dist_le_succ_of_adj h_adj
  
  -- We know G.dist v₀ v_k = k, so G.dist v₀ w ≤ k + 1
  -- Since k < i, then k + 1 ≤ i. This clashes with h_old (≥ i) unless k + 1 = i
  omega



lemma out_neighbors_subset_outNeighbor2 (u_i v_k : V)
    (hk : k < i)
    (hu : u_i ∈ bfsLayerVerts G v₀ i)
    (hv : v_k ∈ bfsLayerVerts G v₀ k)
    (h_back_arc : v_k ∈ N1 G O u_i) :
    N1 G O v_k ⊆ outNeighbor2 G O u_i := by
  rw [Finset.subset_iff]
  intro w hw
  rw [outNeighbor2, Finset.mem_filter]
  constructor
  · -- 1. Show there exists a common intermediate vertex linking them
    rw [Finset.mem_filter] at h_back_arc hw
    use v_k
    exact ⟨h_back_arc.1, hw.1⟩
  · -- 2. Clear the second condition using the metric layer isolation
    -- Split into: w ≠ u_i ∧ w ∉ N1 G O u_i
    constructor
    · intro h_eq
      subst h_eq
      -- If w = u_i, then u_i is an out-neighbor of v_k
      rw [N1, Finset.mem_filter] at hw
      have h_adj := hw.1
      have h_metric := G.dist_le_succ_of_adj h_adj
      simp [bfsLayerVerts] at hu hv
      -- dist(v_k) = k, dist(u_i) = i. Metric implies i ≤ k + 1.
      -- Since k < i, omega flags the arithmetic contradiction.
      omega
    · intro h_in_N1
      rw [N1, Finset.mem_filter] at hw h_in_N1
      have h_adj_vk := hw.1
      have h_adj_ui := h_in_N1.1
      
      -- Extract the distance layers for both paths
      have h_metric_vk := G.dist_le_succ_of_adj h_adj_vk
      have h_metric_ui := G.dist_le_succ_of_adj h_adj_ui
      simp [bfsLayerVerts] at hu hv
      
      -- dist(v_k) = k, so dist(w) ≤ k + 1
      -- Since w is an out-neighbor of u_i, it must hit the forward layer (dist = i + 1)
      -- Knowing k < i, omega catches that k + 1 ≤ i, making i + 1 impossible
      omega


-- Inside your main next_link_backarc_bound theorem:
  have h_union_sub : (outNeighborsOld G O u_i) ∪ (N1 G O v_k) ⊆ outNeighbor2 G O u_i := by
    rw [Finset.union_subset_iff]
    exact ⟨h_sub_old, h_sub_two⟩

  have h_total_card : (outNeighbor2 G O u_i).card ≥ (outNeighborsOld G O u_i).card + (N1 G O v_k).card := by
    -- Calculate card of union via disjointness: card(A ∪ B) = card A + card B
    have h_union_card := Finset.card_union_eq G h_disjoint
    have h_le := Finset.card_le_card h_union_sub
    omega


