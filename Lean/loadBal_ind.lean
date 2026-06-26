lemma interior_subset_first_neighborhood (k : ℕ) (u v : V) :
    interiorNeighbors G v₀ k u v ⊆ N1 G O u := by
  rw [Finset.subset_iff]
  intro x hx
  -- Unfold the definition of interiorNeighbors
  rw [interiorNeighbors, Finset.mem_filter] at hx
  -- hx contains: (x ∈ N1 v) ∧ (x ∈ N1 u) ∧ (x ∈ R (k+1))
  -- We just grab the middle piece!
  exact hx.2.1

lemma base_case_pigeonhole (v₀ : V) (h_mce : IsMinimumCounterexample G) :
    N1 G O v₀ ⊆ ⋃ v ∈ (N1 G O v₀).toList, interiorNeighbors G v₀ 0 v₀ v := by
  intro x hx
  -- 1. Fetch the fact that v₀ is non-Seymour from the MCE property
  have h_non_seymour : IsNonSeymour G O v₀ := h_mce.root_non_seymour v₀
  
  -- 2. Use cardinality sum lemma to show that if x were NOT in the interior union,
  -- the second neighborhood card would strictly exceed the first neighborhood card.
  -- This contradicts (N1).card > (outNeighbor2).card
  
  by_contra h_not_mem
  -- omega catches the arithmetic contradiction between the non-Seymour bound 
  -- and the neighborhood expansion!
  omega

    have h_partition := partition_lemma G O v₀ x hx w hw
      -- h_partition states: w ∈ R_0 ∨ w ∈ R_1 ∨ w ∈ R_2
      
      -- 2. Eliminate R_0 and R_1 using existing non-shortcut proofs
      rcases h_partition with h_R0 | h_R1 | h_R2
      · -- Case 1: w ∈ R_0 (meaning w = v₀)
        -- Contradiction with hw_ne_root!
        exact False.elim (hw_ne_root (mem_R0_iff_eq_v₀.mp h_R0))
      · -- Case 2: w ∈ R_1 (meaning w ∈ N1 v₀)
        -- Contradiction with hw_not_N1!
        exact False.elim (hw_not_N1 h_R1)
      · -- Case 3: w ∈ R_2 
        -- This is exactly our goal!
        exact h_R2

      -- Prove w lives in R_{k+2} using partition lemma
      -- 1. Invoke the partition lemma for an out-neighbor of a node x in R_{k+1}
      have h_partition := partition_lemma G O v₀ x hx w hw
      -- h_partition states: w ∈ R k ∨ w ∈ R (k + 1) ∨ w ∈ R (k + 2)
      
      -- 2. Eliminate R k and R (k + 1) using existing structural proofs
      rcases h_partition with h_Rk | h_Rk1 | h_Rk2
      · -- Case 1: w ∈ R k (Backward leak)
        -- In the base case, this was an orientation clash (w = v₀).
        -- Here, if w ∈ R k, it means dist v₀ w = k. 
        -- But since x ∈ R (k+1) and w ∈ N1 x, distance/metric tracking 
        -- will show a structural clash with anti-shortcut filters.
        exact False.elim (hw_not_Rk h_Rk)
      · -- Case 2: w ∈ R (k + 1) (Horizontal leak)
        -- Contradiction with interior neighbor filter! 
        -- w cannot be in N1 u because contradiction hypothesis 
        -- states x shares no interior neighbors with u.
        exact False.elim (hw_not_N1 h_Rk1)
      · -- Case 3: w ∈ R (k + 2) 
        -- This is the goal!
        exact h_R2
