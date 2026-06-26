
lemma claim_three_density_clamp (v : V) (h_mce : IsMinimumCounterexample G)
    (h_over_degree : (outNeighbor1 G v).card > delta G) :
    False := by
  -- 1. Choose an arbitrary edge 'e' emanating from v into the forward layer
  have h_nonempty : (outNeighbor1 G v).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty, Finset.card_empty] at h_over_degree
    omega
   
  rcases h_nonempty with ⟨w, hw⟩
  let e := Sym2.mk (v, w)
  have h_edge : e ∈ G.edgeSet := by
    -- Resolved: Unpacks adjacency from outNeighbor1 membership
    exact outNeighbor1_mem_edges G v w hw

  -- 2. Prove that after deleting 'e', every node's out-degree remains ≥ delta
  have h_still_valid : ∀ x, (G.deleteEdges {e}).outDegree x ≥ delta G := by
    intro x
    by_cases hx : x = v
    · subst hx
      rw [SimpleGraph.deleteEdges_outDegree_eq_sub_one _ _ h_edge]
      omega
    · by_cases hxw : x = w
      · subst hxw
        rw [SimpleGraph.deleteEdges_outDegree_of_in_edge _ _ h_edge]
        exact G.outDegree_geq_delta_of_mce h_mce w
      · rw [SimpleGraph.deleteEdges_outDegree_of_unrelated hx hxw]
        exact G.outDegree_geq_delta_of_mce h_mce x

  -- 3. Pass to the master contradiction engine
  exact mce_edge_deletion_contradiction G h_mce e h_edge h_still_valid
