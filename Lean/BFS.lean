import Std.Data.HashSet

/--
  Computes the shortest path distances from a `start` node to all other nodes 
  in a graph using Breadth-First Search.
  
  - `graph`: An array where `graph[i]` is a list of neighbors for node `i`.
  - `start`: The starting node index.
  - Returns: An array of `Option Nat`, where `some d` is the distance and `none` is unreachable.
-/
def bfsDistances (graph : Array (List Nat)) (start : Nat) : Array (Option Nat) := Id.run do
  -- Initialize all distances to `none` (unreachable / infinity)
  let mut distances := Array.mkArray graph.size none
  let mut visited : Std.HashSet Nat := Std.HashSet.empty
  let mut queue : List Nat := []

  -- Setup the start node if it exists within the graph bounds
  if h : start < graph.size then
    distances := distances.set ⟨start, h⟩ (some 0)
    visited := visited.insert start
    queue := [start]

  -- Core BFS Loop
  while !queue.isEmpty do
    match queue with
    | [] => break
    | curr :: tail =>
      queue := tail

      -- Ensure the current node is valid within the graph bounds
      if hCurr : curr < graph.size then
        -- Retrieve the current distance (we know it exists because it was queued)
        let currentDist := distances[curr]!.getD 0
        let neighbors := graph[curr]

        for neighbor in neighbors do
          if !visited.contains neighbor then
            visited := visited.insert neighbor
            queue := queue ++ [neighbor] -- Enqueue neighbor
            
            -- Update neighbor's distance if it's within bounds
            if hNeigh : neighbor < distances.size then
              distances := distances.set ⟨neighbor, hNeigh⟩ (some (currentDist + 1))

  return distances

-- A clean coordinate mapper using pairs
def bfsLexPairs (graph : Array (List Nat)) (start : Nat) : Array (Nat × Nat) := Id.run do
  let dists := bfsDistances graph start
  let mut ids := Array.mkArray graph.size (0, 0)
  for i in [0:graph.size] do
    let d := match dists[i]! with
      | some d => d
      | none   => 99999 -- Or a sufficiently large infinity bound
    ids := ids.set! i (d, i)
  return ids


import Std.Data.List.Basic

-- Define our coordinate comparison (distance, index)
def nodeLessFromCoord (c1 c2 : Nat × Nat) : Bool :=
  if c1.1 < c2.1 then true
  else if c1.1 == c2.1 then c1.2 < c2.2
  else false

-- The core minimum-finding function operating on our remaining dataset H
def getMinCoord (H : List (Nat × Nat)) : Option (Nat × Nat) :=
  match H with
  | [] => none
  | first :: tail => 
    some (tail.foldl (fun currentMin next => 
      if nodeLessFromCoord next currentMin then next else currentMin) first)

---

## The Core Mathematical Engine

/-- 
  Inductive Lemma: If a subset H is sorted lexicographically, 
  the minimum element found by our loop is always its first element (the head).
-/
lemma min_eq_head_of_sorted (H : List (Nat × Nat)) 
    (h_sorted : H.Sorted (fun p1 p2 => p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2))) :
    H ≠ [] → getMinCoord H = H.head? := by
  intro h_nonempty
  rcases H with | [] => contradiction | first :: tail =>
    dsimp [getMinCoord, List.head?]
    congr
    -- Prove the loop invariant via induction on the remaining elements
    generalize h_init : first = init
    have h_min : ∀ x ∈ tail, (nodeLessFromCoord x init) = false := by
      intro x hx
      -- Extract the sorted relation for the tail elements
      have h_rel := List.Sorted.rel_of_mem hx h_sorted
      rw [← h_init] at h_rel
      -- Unfold the boolean check and match it against the sorted hypothesis
      dsimp [nodeLessFromCoord]
      split_ifs with h1 h2
      · -- Case 1: x.1 < first.1, which contradicts first.1 < x.1 or first.1 = x.1
        rcases h_rel with h_lt | ⟨h_eq, _⟩
        · exact (Nat.lt_asymm h1 h_lt).elim
        · rw [h_eq] at h1; exact (Nat.lt_irrefl _ h1).elim
      · -- Case 2: x.1 == first.1 and x.2 < first.2
        rw [Nat.beq_eq] at h2
        rcases h_rel with h_lt | ⟨_, h_sub_lt⟩
        · rw [h2] at h_lt; exact (Nat.lt_irrefl _ h_lt).elim
        · exact (Nat.lt_asymm h1 h_sub_lt).elim-- Error handling helper
      · rfl
    clear h_sorted h_nonempty
    induction tail generalizing init with
    | nil => rfl
    | cons next xs ih =>
      dsimp [List.foldl]
      have h_next := h_min next (List.mem_cons_self _ _)
      rw [h_next] -- The 'if' condition evaluates to false, choosing 'init'
      apply ih
      intro x hx
      exact h_min x (List.mem_cons_of_mem _ hx)

---

## Formalizing Your Two Mathematical Cases

/-- 
  CASE 1: The root belongs to H.
  The root has a BFS distance of 0, meaning it naturally sits at the head 
  of the sorted subset and is identified as the global minimum.
-/
theorem case_1_root_in_subgraph (H : List (Nat × Nat)) (root_idx : Nat)
    (h_sorted : H.Sorted (fun p1 p2 => p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)))
    (h_root : (0, root_idx) ∈ H) (h_head : H.head? = some (0, root_idx)) :
    getMinCoord H = some (0, root_idx) := by
  have h_nonempty : H ≠ [] := by 
    intro h; rw [h] at h_head; contradiction
  rw [min_eq_head_of_sorted H h_sorted h_nonempty]
  exact h_head

/-- 
  CASE 2: The root does not belong to H.
  The root is missing, but H remains inherently sorted. The first element 
  of H, say (k, l), has the lowest remaining distance and lowest lexicographical 
  node index at that distance, making it the new global minimum.
-/
theorem case_2_root_not_in_subgraph (H : List (Nat × Nat)) (k l : Nat)
    (h_sorted : H.Sorted (fun p1 p2 => p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)))
    (h_no_root : ∀ x ∈ H, x.1 ≠ 0) (h_head : H.head? = some (k, l)) :
    getMinCoord H = some (k, l) := by
  have h_nonempty : H ≠ [] := by 
    intro h; rw [h] at h_head; contradiction
  -- Even without a root, the head of a sorted list is the absolute minimum
  rw [min_eq_head_of_sorted H h_sorted h_nonempty]
  exact h_head
/-- 
  CASE 2: The root does not belong to H.
  The root is missing, but H remains inherently sorted. The first element 
  of H, say (k, l), has the lowest remaining distance and lowest lexicographical 
  node index at that distance, making it the new global minimum.
-/
theorem case_2_root_not_in_subgraph (H : List (Nat × Nat)) (k l : Nat)
    (h_sorted : H.Sorted (fun p1 p2 => p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)))
    (h_no_root : ∀ x ∈ H, x.1 ≠ 0) (h_head : H.head? = some (k, l)) :
    getMinCoord H = some (k, l) := by
  have h_nonempty : H ≠ [] := by 
    intro h; rw [h] at h_head; contradiction
  -- Even without a root, the head of a sorted list is the absolute minimum
  rw [min_eq_head_of_sorted H h_sorted h_nonempty]
  exact h_head


/--
  Theorem: If there is an edge from u to v, v cannot belong to a "later layer"
  (any layer b ≥ a + 2).
-/
lemma later_neighbors_impossible (u v : Nat) (a b : Nat)
    (hu : u ∈ bfsLayerVerts G v₀ a) 
    (hv : v ∈ bfsLayerVerts G v₀ b)
    (h_edge : v ∈ G.neighbors u) 
    (h_later : b ≥ a + 2) : False := by
  -- 1. Unfold your layer definitions (similar to your simp [bfsLayerVerts] step)
  -- This gives you: G.dist v₀ u = a  and  G.dist v₀ v = b
  have hu_dist : G.dist v₀ u = a := by ...
  have hv_dist : G.dist v₀ v = b := by ...

  -- 2. Use the graph's shortest path property: 
  -- The distance to v is at most the distance to u + 1
  have h_triangle : G.dist v₀ v ≤ G.dist v₀ u + 1 := G.dist_neighbor_le h_edge

  -- 3. Substitute your layer indexes into the inequality
  rw [hu_dist, hv_dist] at h_triangle

  -- 4. Let omega handle the contradiction!
  -- We have (b ≤ a + 1) and (b ≥ a + 2), which omega crushes instantly.
  omega
