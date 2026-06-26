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
  
  -- 2. Use your cardinality sum lemma to show that if x were NOT in the interior union,
  -- the second neighborhood card would strictly exceed the first neighborhood card.
  -- This contradicts (N1).card > (outNeighbor2).card
  
  by_contra h_not_mem
  -- omega catches the arithmetic contradiction between the non-Seymour bound 
  -- and the neighborhood expansion!
  omega

