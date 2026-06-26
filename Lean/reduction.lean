/-- Part 1 & 3: The Definitional Containments (⊇)
    No matter the layer, any exterior or back neighbor of a child is 
    structurally a second neighbor of the parent. -/
lemma reduction_definition_containment (k : ℕ) (u v : V) (hu : u ∈ bfsLayerVerts G v₀ k) (hv : v ∈ N1 G O u) :
    (exteriorNeighbors G v₀ k u v) ∪ (backNeighbors G v₀ k v) ⊆ outNeighbor2 G O u := by
  rw [Finset.union_subset_iff]
  constructor
  · -- Subcase A: Exterior neighbors land in outNeighbor2
    rw [Finset.subset_iff]; intro x hx
    rw [exteriorNeighbors, Finset.mem_filter] at hx
    rw [outNeighbor2, Finset.mem_filter]
    exact ⟨⟨v, hv, hx.1⟩, hx.2.2⟩ -- returns the path and non-shortcut condition
  · -- Subcase B: Back neighbors land in outNeighbor2
    rw [Finset.subset_iff]; intro x hx
    rw [backNeighbors, Finset.mem_filter] at hx
    rw [outNeighbor2, Finset.mem_filter]
    exact ⟨⟨v, hv, hx.1⟩, hx.2.2⟩

lemma reduction_definition_containment (k : ℕ) (u v : V) 
    (hu : u ∈ bfsLayerVerts G v₀ k) (hv : v ∈ N1 G O u) :
    (exteriorNeighbors G v₀ k u v) ∪ (backNeighbors G v₀ k v) ⊆ outNeighbor2 G O u := by
  rw [Finset.union_subset_iff]
  constructor
  · -- Subcase A: Exterior neighbors are second neighbors
    rw [Finset.subset_iff]
    intro x hx
    rw [exteriorNeighbors, Finset.mem_filter] at hx
    rw [outNeighbor2, Finset.mem_filter]
    -- hx gives: (v → x) ∧ (x ≠ u) ∧ (x ∉ N1 u) ∧ (x ∈ R_{k+2})
    constructor
    · -- 1. Provide the path u → v → x
      use v
      exact ⟨hv, hx.1⟩
    · -- 2. Provide the anti-shortcut conditions
      exact ⟨hx.2.1, hx.2.2.1⟩

  · -- Subcase B: Back neighbors are second neighbors
    rw [Finset.subset_iff]
    intro x hx
    rw [backNeighbors, Finset.mem_filter] at hx
    rw [outNeighbor2, Finset.mem_filter]
    -- hx gives: (v → x) ∧ (x ≠ u) ∧ (x ∉ N1 u) ∧ (x ∈ R_{<k})
    constructor
    · -- 1. Provide the path u → v → x
      use v
      exact ⟨hv, hx.1⟩
    · -- 2. Provide the anti-shortcut conditions
      exact ⟨hx.2.1, hx.2.2.1⟩

/-- Part 2: Base Case Partition Collapse (⊆)
    When k = 0, back-arcs cannot exist past the root, so the back component drops out. -/
lemma reduction_base_case_pigeonhole (v₀ : V) :
    outNeighbor2 G O v₀ ⊆ ⋃ v ∈ (N1 G O v₀).toList, exteriorNeighbors G v₀ 0 v₀ v := by
  rw [Finset.subset_iff]
  intro x hx
  rw [outNeighbor2, Finset.mem_filter] at hx
  rcases hx.1 with ⟨v, hv, h_edge⟩ -- v is the intermediate child node v₀ -> v -> x
  
  rw [Set.mem_iUnion]
  use v
  rw [List.mem_to_list]
  refine ⟨hv, ?_⟩
  
  -- Use the Partition Lemma to show x MUST live in R_2
  have h_partition := partition_lemma G O v₀ v hv x h_edge
  rcases h_partition with h_R0 | h_R1 | h_R2
  · -- Case 1: x ∈ R_0 (meaning x = v₀). Clashes with outNeighbor2 non-shortcut!
    sorry 
  · -- Case 2: x ∈ R_1 (meaning x ∈ N1 v₀). Clashes with outNeighbor2 non-shortcut!
    sorry
  · -- Case 3: x ∈ R_2. This matches the exact definition of exteriorNeighbors!
    rw [exteriorNeighbors, Finset.mem_filter]
    exact ⟨h_edge, by sorry⟩

/-- The Main Overarching Reduction Theorem -/
theorem reduction_theorem (G : SimpleGraph V) [DecidableRel G.Adj] 
    (h_mce : IsMinimumCounterexample G) (k : ℕ) (u : V) (hu : u ∈ bfsLayerVerts G v₀ k) :
    outNeighbor2 G O u = (⋃ v ∈ (N1 G O u).toList, exteriorNeighbors G v₀ k u v) ∪ 
                         (⋃ v ∈ (N1 G O u).toList, backNeighbors G v₀ k v) := by
  induction k generalizing u with
  | zero => 
    -- Base Case (k = 0)
    ext x
    constructor
    · -- Part 2: Base Case Partition Collapse
      sorry 
    · -- Part 1: Definition Containment
      sorry
  | succ k ih => 
    -- Inductive Step (k + 1)
    ext x
    constructor
    · -- Part 4: Inductive Partition Squeeze
      -- Partition lemma splits x into R_k (back) or R_{k+2} (exterior)
      sorry
    · -- Part 3: Definition Containment
      sorry

lemma reduction_base_case_pigeonhole (v₀ : V) :
    outNeighbor2 G O v₀ ⊆ ⋃ v ∈ (N1 G O v₀).toList, exteriorNeighbors G v₀ 0 v₀ v := by
  rw [Finset.subset_iff]
  intro x hx
  -- Unpack the second neighborhood definition: there is a path v₀ -> v -> x
  rw [outNeighbor2, Finset.mem_filter] at hx
  rcases hx.1 with ⟨v, hv, h_edge⟩ 
  have h_not_N1 := hx.2.2  -- x is not a first neighbor of v₀
  have h_ne_root := hx.2.1  -- x is not v₀ itself
  
  -- Open the target union and choose the intermediate node `v` as the witness
  rw [Set.mem_iUnion]
  use v
  rw [List.mem_to_list]
  refine ⟨hv, ?_⟩
  
  -- Invoke the Partition Lemma on the edge v -> x where v ∈ R_1
  have h_partition := partition_lemma G O v₀ v hv x h_edge
  rcases h_partition with h_R0 | h_R1 | h_R2
  · -- Case 1: x ∈ R_0. By definition of R_0, this means x = v₀.
    -- This directly clashes with our second neighbor property (h_ne_root).
    have h_eq : x = v₀ := mem_R0_iff_eq_v₀.mp h_R0
    exact False.elim (h_ne_root h_eq)
    
  · -- Case 2: x ∈ R_1. By definition of R_1, this means x ∈ N1 G O v₀.
    -- This directly clashes with our anti-shortcut filter (h_not_N1).
    exact False.elim (h_not_N1 h_R1)
    
  · -- Case 3: x ∈ R_2. This is exactly where x belongs!
    -- Unfold exteriorNeighbors to verify it matches the structural properties we hold.
    rw [exteriorNeighbors, Finset.mem_filter]
    exact ⟨h_edge, h_ne_root, h_not_N1, h_R2⟩

lemma reduction_inductive_step_squeeze (k : ℕ) (u : V) (hu : u ∈ bfsLayerVerts G v₀ (k + 1)) :
    outNeighbor2 G O u ⊆ (⋃ v ∈ (N1 G O u).toList, exteriorNeighbors G v₀ (k + 1) u v) ∪ 
                         (⋃ v ∈ (N1 G O u).toList, backNeighbors G v₀ (k + 1) v) := by
  rw [Finset.subset_iff]
  intro w hw
  rw [outNeighbor2, Finset.mem_filter] at hw
  rcases hw.1 with ⟨v, hv, h_edge⟩ -- path: u → v → w
  have hw_ne := hw.2.1
  have hw_not_N1 := hw.2.2

  -- Invoke the partition lemma for v ∈ R_{k+2} (since u ∈ R_{k+1})
  have hv_layer : v ∈ bfsLayerVerts G v₀ (k + 2) := by sorry -- given by u ∈ R_{k+1} and v ∈ N1 u
  have h_partition := partition_lemma G O v₀ v hv_layer w h_edge
  -- h_partition states: w ∈ R_{k+1} ∨ w ∈ R_{k+2} ∨ w ∈ R_{k+3}
  
  rw [Set.mem_union]
  rcases h_partition with h_Rk1 | h_Rk2 | h_Rk3
  · -- Case 1: w leaks horizontally into R_{k+1}
    -- This means w ∈ N1 G O u, which directly contradicts hw_not_N1
    have hw_in_N1 : w ∈ N1 G O u := by sorry -- structural check via lower_layer_neighbors_disjoint
    exact False.elim (hw_not_N1 hw_in_N1)

  · -- Case 2: w leaks backward into a lower layer R_{k+2} relative to v
    -- This places w in backNeighbors
    right
    rw [Set.mem_iUnion]
    use v
    rw [List.mem_to_list]
    refine ⟨hv, ?_⟩
    rw [backNeighbors, Finset.mem_filter]
    exact ⟨h_edge, hw_ne, hw_not_N1, h_Rk2⟩

  · -- Case 3: w goes forward into R_{k+3}
    -- This places w in exteriorNeighbors
    left
    rw [Set.mem_iUnion]
    use v
    rw [List.mem_to_list]
    refine ⟨hv, ?_⟩
    rw [exteriorNeighbors, Finset.mem_filter]
    exact ⟨h_edge, hw_ne, hw_not_N1, h_Rk3⟩
