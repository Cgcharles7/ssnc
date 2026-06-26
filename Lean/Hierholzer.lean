import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Basic

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (v₀ : V) (i k : ℕ)
/-- Hierholzer's structural guarantee formalized via edge-cardinality induction. -/
lemma interior_neighborhood_cycle_decomposition (u_k : V) 
    (h_balanced : ∀ v ∈ interiorNeighbors G v₀ i k u_k u_k, 
      inDegree_local G v₀ i k v = outDegree_local G v₀ i k v) :
    ∃ (C : List (List V)), (∀ c ∈ C, IsCycle G c) ∧ (∀ e ∈ localEdgeSet G v₀ i k, ∃ c ∈ C, e ∈ edgesOfC c) := by
  
  -- 1. Generalize the cardinality to a natural number 'm' and induct on it
  generalize h_card : (localEdgeSet G v₀ i k).card = m
  induction m generalizing G with
  | zero => 
    -- Base Case: m = 0
    use []
    intro e he
    rw [← h_card, Finset.card_eq_zero] at he
    -- he says: e ∈ ∅, which is a contradiction
    exact Finset.not_mem_empty e he

  | succ m ih =>
    -- Inductive Step: m + 1

  | succ m ih =>
    -- Inductive Step: There is at least one edge, so there must be a cycle.
    -- A. Extract a single cycle C₀ from the balanced finite local graph
    have h_exists_cycle : ∃ c₀, IsCycle G c₀ ∧ (∀ e ∈ edgesOfC c₀, e ∈ localEdgeSet G v₀ i k) := by
      -- Balanced, non-empty directed/local graphs always contain at least one simple cycle
      sorry

    rcases h_exists_cycle with ⟨c₀, hc₀_cycle, hc₀_sub⟩
    
    -- B. Peeling out C₀ leaves a smaller graph G' that is still perfectly balanced
    let G_prime := G.deleteEdges (edgesOfC c₀)
    have h_card_drop : (localEdgeSet G_prime v₀ i k).card = m := by
      -- Subtracting the edges of c₀ strictly decreases the edge card by the length of c₀
      sorry
      
    have h_prime_balanced : ∀ v ∈ interiorNeighbors G_prime v₀ i k u_k u_k, 
        inDegree_local G_prime v₀ i k v = outDegree_local G_prime v₀ i k v := by
      intro v hv
      
      -- 1. Fetch the original balance state for node v
      have h_orig := h_balanced v (mem_interiorNeighbors_of_mem_G_prime hv)
      
      -- 2. Convert local graph deletion directly into natural number subtraction
      rw [inDegree_local, Finset.card_sdiff (hc₀_sub v)]
      rw [outDegree_local, Finset.card_sdiff (hc₀_sub v)]
      
      -- 3. Case split on whether the cycle c₀ passes through vertex v
      by_cases hv_in_c₀ : v ∈ c₀
      · -- Case A: v is on the cycle. The cycle peels away exactly 1 edge from each side.
        have h_in_peel : (edgesOfC c₀).filter (λ e => e.2 = v).card = 1 := 
          cycle_inDegree_eq_one_of_mem hc₀_cycle hv_in_c₀
        have h_out_peel : (edgesOfC c₀).filter (λ e => e.1 = v).card = 1 := 
          cycle_outDegree_eq_one_of_mem hc₀_cycle hv_in_c₀
        
        rw [h_in_peel, h_out_peel]
        -- Lean evaluates: deg_in - 1 = deg_out - 1. Since deg_in = deg_out, omega closes it!
        omega
        
      · -- Case B: v is NOT on the cycle. The cycle peels away 0 edges from both sides.
        have h_in_peel : (edgesOfC c₀).filter (λ e => e.2 = v).card = 0 := by
          rw [Finset.card_eq_zero]
          exact cycle_inDegree_eq_zero_of_not_mem hc₀_cycle hv_in_c₀
        have h_out_peel : (edgesOfC c₀).filter (λ e => e.1 = v).card = 0 := by
          rw [Finset.card_eq_zero]
          exact cycle_outDegree_eq_zero_of_not_mem hc₀_cycle hv_in_c₀
          
        rw [h_in_peel, h_out_peel]
        -- Lean evaluates: deg_in - 0 = deg_out - 0, which is just h_orig!
        exact h_orig

    -- C. Apply the induction hypothesis to the remaining balanced graph G'
    rcases ih G_prime h_prime_balanced h_card_drop with ⟨C_prime, h_cycles_prime, h_edges_prime⟩
    
    -- D. Cons the isolated cycle c₀ onto the front of the rest of the collection
    use c₀ :: C_prime
    constructor
    · -- Verify all elements are valid cycles
      intro c hc
      rcases List.mem_cons.mp hc with rfl | h_mem
      · exact hc₀_cycle
      · -- Must shift cycle legality back to original graph G (deleting edges preserves underlying simple graph types)
        exact IsCycle_of_IsCycle_deleteEdges (h_cycles_prime c h_mem)
    · -- Verify all original edges are caught by the decomposition
      intro e he
      by_cases he_in_c₀ : e ∈ edgesOfC c₀
      · use c₀
        exact ⟨List.mem_cons_self c₀ C_prime, he_in_c₀⟩
      · have he_prime : e ∈ localEdgeSet G_prime v₀ i k := by sorry -- It wasn't deleted, so it's in G'
        rcases h_edges_prime e he_prime with ⟨c, hc_mem, he_in_c⟩
        use c
        exact ⟨List.mem_cons_of_mem c₀ hc_mem, he_in_c⟩
