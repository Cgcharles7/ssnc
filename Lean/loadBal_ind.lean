lemma base_case_definition (v₀ v : V) :
    interiorNeighbors G v₀ 0 v₀ v ⊆ N1 G O v₀ := by
  rw [Finset.subset_iff]
  intro x hx
  rw [interiorNeighbors, Finset.mem_filter] at hx
  exact hx.2.1

lemma inductive_case_definition (k : ℕ) (u v : V) :
    interiorNeighbors G v₀ k u v ⊆ N1 G O u := by
  rw [Finset.subset_iff]
  intro x hx
  rw [interiorNeighbors, Finset.mem_filter] at hx
  exact hx.2.1

lemma base_case_pigeonhole (v₀ : V) (h_mce : IsMinimumCounterexample G) :
    N1 G O v₀ ⊆ ⋃ v ∈ (N1 G O v₀).toList, interiorNeighbors G v₀ 0 v₀ v := by
  intro x hx
  have h_non_seymour : IsNonSeymour G O v₀ := h_mce.root_non_seymour v₀
  
  by_contra h_not_mem
  rw [Set.mem_iUnion] at h_not_mem
  push_neg at h_not_mem

  -- Bridge: Prove N1 G O x ⊆ outNeighbor2 G O v₀ via local layer elimination
  have h_sub : N1 G O x ⊆ outNeighbor2 G O v₀ := by
    rw [Finset.subset_iff]
    intro w hw
    rw [outNeighbor2, Finset.mem_filter]
    constructor
    · rw [secondNeighborSet]
      have h_path : ∃ z, z ∈ N1 G O v₀ ∧ w ∈ N1 G O z := ⟨x, hx, hw⟩
      have hw_ne_root : w ≠ v₀ := by
        intro h_eq; subst h_eq
        exact O.asymmetric hx hw
      have hw_not_N1 : w ∉ N1 G O v₀ := by
        intro h_in_N1
        have h_is_int : w ∈ interiorNeighbors G v₀ 0 v₀ x := by
          rw [interiorNeighbors, Finset.mem_filter]
          exact ⟨hw, h_in_N1, by sorry⟩ -- structural layer 1 check
        exact h_not_mem x hx h_is_int
      exact ⟨hw_ne_root, hw_not_N1, h_path⟩
    · -- The Partition Lemma locks down layer 2
      have h_partition := partition_lemma G O v₀ x hx w hw
      rcases h_partition with h_R0 | h_R1 | h_R2
      · exact False.elim (hw_ne_root (mem_R0_iff_eq_v₀.mp h_R0))
      · exact False.elim (hw_not_N1 h_R1)
      · exact h_R2

  -- Target cardinality comparison for omega's Seymour Trap
  have h_child_deg : (N1 G O x).card ≥ delta G := G.min_degree_le_degree x
  have h_R2_size : (outNeighbor2 G O v₀).card ≥ delta G := by
    have h_le := Finset.card_le_card h_sub
    omega
    
  omega

-- Prove w lives in R_{k+2} using partition lemma
  -- 1. Invoke the partition lemma for an out-neighbor of a node x in R_{k+1}
  have h_partition := partition_lemma G O v₀ x hx w hw
  -- h_partition states: w ∈ R k ∨ w ∈ R (k + 1) ∨ w ∈ R (k + 2)
  
  -- 2. Eliminate R k and R (k + 1) using existing structural proofs
  rcases h_partition with h_Rk | h_Rk1 | h_Rk2
  · -- Case 1: w ∈ R k (Backward leak)
    -- Contradiction with anti-shortcut filters
    exact False.elim (hw_not_Rk h_Rk)
  · -- Case 2: w ∈ R (k + 1) (Horizontal leak)
    -- Contradiction with interior neighbor filter hypothesis
    exact False.elim (hw_not_N1 h_Rk1)
  · -- Case 3: w ∈ R (k + 2) 
    -- This is the goal!
    exact h_Rk2
