-- Proving the Set Equality via Double Inclusion
· ext w
  constructor
  · -- Direction 1: Left to Right (⊆)
    intro hw
    rw [outNeighbor1, Set.mem_setOf_eq] at hw -- gives the edge v → w
    -- Extract BFS triangle inequality: |dist(w) - dist(v)| ≤ 1
    have h_metric := G.dist_le_succ_of_adj hw
    have h_cases : G.dist v₀ w ≤ i ∨ G.dist v₀ w = i + 1 ∨ G.dist v₀ w = i + 2 := by
      -- Since dist(v) = i + 1, omega solves the bounds allowed by h_metric
      omega
    rcases h_cases with h_back_case | h_int_case | h_ext_case
    · left; rw [backNeighbors, Set.mem_setOf_eq]; exact ⟨hw, h_back_case⟩
    · right; left; rw [interiorNeighbors, Set.mem_setOf_eq]; exact ⟨hw, h_int_case⟩
    · right; right; rw [exteriorNeighbors, Set.mem_setOf_eq]; exact ⟨hw, h_ext_case⟩
   
  · -- Direction 2: Right to Left (⊇)
    intro hw
    rcases hw with h_back | h_int | h_ext
    · rw [backNeighbors, Set.mem_setOf_eq] at h_back; exact h_back.left
    · rw [interiorNeighbors, Set.mem_setOf_eq] at h_int; exact h_int.left
    · rw [exteriorNeighbors, Set.mem_setOf_eq] at h_ext; exact h_ext.left

lemma layers_disjoint (a b : ℕ) (h_ne : a ≠ b) :
    Disjoint (bfsLayerVerts G v₀ a) (bfsLayerVerts G v₀ b) := by
  rw [Set.disjoint_iff_forall_not_mem]
  intro x hx
  rcases hx with ⟨ha, hb⟩
  -- ha forces: G.dist v₀ x = a
  -- hb forces: G.dist v₀ x = b
  simp [bfsLayerVerts] at ha hb
  -- Conclude via equality transitivity: a = b, which contradicts h_ne
  omega

lemma local_edges_disjoint_from_previous (k : ℕ) (v : V) (hv : v ∈ bfsLayerVerts G v₀ (k + 1)) :
    Disjoint
      ((G.induce (verticesUpTo G v₀ k)).edgeFinset)
      (((G.induce (verticesUpTo G v₀ (k + 1))).edgeFinset).filter (fun e => v ∈ e)) := by
  rw [Finset.disjoint_iff_forall_not_mem]
  intro e he
  rcases he with ⟨h_prev, h_local⟩
  rw [Finset.mem_filter] at h_local
 
  -- 1. h_prev forces both endpoints of e to have distance ≤ k
  have h_endpoints_prev : ∀ x ∈ e, dist v₀ x ≤ k := by
    intro x hx
    -- e is in the edge set of the induced subgraph
    rw [SimpleGraph.induce_edgeFinset_iff] at h_prev
    -- Therefore, both endpoints of e must be in 'verticesUpTo G v₀ k'
    have h_in_set := h_prev.1 x hx
    rw [verticesUpTo, Finset.mem_filter] at h_in_set
    exact h_in_set.2
 
  -- 2. h_local forces v to be one of the endpoints, meaning v ∈ e
  have h_v_in_e : v ∈ e := h_local.2
 
  -- 3. This implies G.dist v₀ v ≤ k
  have h_v_dist := h_endpoints_prev v h_v_in_e
 
  -- 4. Contradiction: hv states v ∈ R_{k+1}, so G.dist v₀ v = k + 1
  simp [bfsLayerVerts] at hv
  omega

-- Fix 1 applied inside partition theorem:
· intro hw
    rw [outNeighbor1, Set.mem_setOf_eq] at hw
    -- 1. Unpack the exact distance of v
    have hv_dist : G.dist v₀ v = i + 1 := by
      simp [bfsLayerVerts] at hv; exact hv
   
    -- 2. Get the forward triangle inequality: dist(w) ≤ dist(v) + 1
    have h_metric_forward := G.dist_le_succ_of_adj hw
   
    -- 3. Get the backward triangle inequality: dist(v) ≤ dist(w) + 1
    -- (Since SimpleGraph edges are symmetric, if G.Adj v w, then G.Adj w v)
    have h_metric_backward := G.dist_le_succ_of_adj (G.symm hw)
   
    -- 4. Now omega has everything it needs to clamp the distance
    have h_cases : G.dist v₀ w ≤ i ∨ G.dist v₀ w = i + 1 ∨ G.dist v₀ w = i + 2 := by
      omega
     
    rcases h_cases with h_back_case | h_int_case | h_ext_case
    · left; rw [backNeighbors, Set.mem_setOf_eq]; exact ⟨hw, h_back_case⟩
    · right; left; rw [interiorNeighbors, Set.mem_setOf_eq]; exact ⟨hw, h_int_case⟩
    · right; right; rw [exteriorNeighbors, Set.mem_setOf_eq]; exact ⟨hw, h_ext_case⟩

-- Fix 2 applied to clear previous lemma's sorry:
lemma local_edges_disjoint_from_previous (k : ℕ) (v : V) (hv : v ∈ bfsLayerVerts G v₀ (k + 1)) :
    Disjoint
      ((G.induce (verticesUpTo G v₀ k)).edgeFinset)
      (((G.induce (verticesUpTo G v₀ (k + 1))).edgeFinset).filter (fun e => v ∈ e)) := by
  rw [Finset.disjoint_iff_forall_not_mem]
  intro e he
  rcases he with ⟨h_prev, h_local⟩
  rw [Finset.mem_filter] at h_local
 
  -- Sorry Cleared Here:
  have h_endpoints_prev : ∀ x ∈ e, G.dist v₀ x ≤ k := by
    rw [SimpleGraph.mem_induce_edgeFinset] at h_prev
    intro x hx
    have h_in_set := h_prev.2 x hx
    simp [verticesUpTo] at h_in_set
    exact h_in_set
 
  have h_v_in_e : v ∈ e := h_local.2
  have h_v_dist := h_endpoints_prev v h_v_in_e
  simp [bfsLayerVerts] at hv
  omega


/-- Lemma 5: Side Neighbors Cannot Exist in Rooted Neighborhoods -/
theorem no_side_neighbors (i : ℕ) (u v : V) 
    (hu : u ∈ bfsLayerVerts G v₀ i) 
    (hv : v ∈ bfsLayerVerts G v₀ (i + 1)) 
    (huv : O.as_rel u v) :
    sideNeighbors G O v₀ i u v = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro w hw
  
  -- 1. Unpack: "Let w be a side neighbor of u"
  rw [sideNeighbors, mem_filter] at hw
  rcases hw with ⟨hw_in_N1, h_not_u_link, h_not_u, dist_w⟩
  
  -- Extract that v connects to w (from w ∈ N1 v)
  rw [N1, mem_filter] at hw_in_N1
  have h_vw_edge : O.as_rel v w := hw_in_N1.2
  
  -- 2. Gather distances: "u is at distance i, v is at distance i+1"
  rw [bfsLayerVerts, mem_filter] at hu hv
  have dist_u : dist v₀ u = i := hu.2
  have dist_v : dist v₀ v = i + 1 := hv.2
  
  -- 3. Shortest path from u to w is bounded by 2 (via u -> v -> w)
  have h_uw_bound : dist v₀ w ≤ dist v₀ u + 2 := by
    have h1 := dist_edge_bound G O v₀ u v huv
    have h2 := dist_edge_bound G O v₀ v w h_vw_edge
    omega
    
  -- 4. Unpack w's layer information to show dist v₀ w = i + 1
  rw [bfsLayerVerts, mem_filter] at dist_w
  have dist_w_val : dist v₀ w = i + 1 := dist_w.2

  -- 5. The Trap Snaps: substitute our known distances into the bound
  rw [dist_u, dist_w_val] at h_uw_bound
  
  -- Because w is NOT a first neighbor of u (h_not_u_link) and not u itself,
  -- and it is discovered through v, its distance must step out to i + 2.
  -- This forces the arithmetic contradiction: i + 1 = i + 2
  omega
