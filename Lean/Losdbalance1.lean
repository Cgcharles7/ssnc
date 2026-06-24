
lemma load_balance_inductive_step_claim_one (k : ℕ) (u_k v : V)
    (h_mce : IsMinimumCounterexample G)
    (hu : u_k ∈ R k)
    (hv : v ∈ N1 G O u_k)
    (h_IH : card (N1 G O u_k) = delta G - k + 1) -- Linear decay size from IH
    (h_partition : card (N1 G O v) = card (backNeighbors G v₀ k v) + card (localNeighbors G v₀ k v) + card (forwardNeighbors G v₀ k v))
    (h_back : card (backNeighbors G v₀ k v) ≥ 1)
    (h_reg : card (N1 G O v) = delta G) :
    card (localNeighbors G v₀ k v) ≥ k := by
  -- 1. Start the proof by contradiction
  by_contra h_lt
  push_neg at h_lt -- Gives: card (localNeighbors G v₀ k v) ≤ k - 1

  -- 2. Invoke the arithmetic spike lemma
  have h_spike : card (forwardNeighbors G v₀ k v) > delta G - k := by
    omega

  -- 3. Connect the forward neighbors to the parent's second neighborhood
  have h_subset : card (forwardNeighbors G v₀ k v) ≤ card (outNeighbor2 G u_k) := by
    -- Forward neighbors of a child are strictly inside the second neighborhood of the parent
    exact card_le_card_forward_to_neighborhood2 G v₀ k u_k v hu hv

  -- 4. Calculate the Seymour violation using omega
  have h_seymour_card : card (outNeighbor2 G u_k) ≥ card (N1 G O u_k) := by
    omega -- Compares (spike: > delta - k) with (IH: = delta - k + 1)

  -- 5. Trigger the MCE Contradiction
  have h_is_seymour : IsSeymour G u_k := by
    rw [IsSeymour]
    exact h_seymour_card

  -- Pull the MCE property: No vertex can be Seymour
  have h_no_seymour := h_mce.no_seymour_verts u_k
  exact h_no_seymour h_is_seymour
