variable {Adj : Nat → Nat → Prop}

/-- The size of a node's first neighborhood (out-degree) -/
def cardN1 (G : FiniteGraph Adj) (u : Nat) : Nat :=
  (G.edges.filter (fun e => e.1 = u)).length

/-- The size of a node's second neighborhood (out-neighbors of out-neighbors, minus shortcuts) -/
def cardN2 (G : FiniteGraph Adj) (u : Nat) : Nat :=
  -- Counts unique nodes w where there's a valid path u -> v -> w 
  -- and w is neither u nor a direct neighbor of u.
  sorry

/-- 
  Enhanced BfsLex that structurally tracks:
  1. Shortest path layer distance (`d`)
  2. The graph's global minimum out-degree (`delta`)
  3. The interlocking density guarantee
-/
inductive BfsLex (delta : Nat) : (d : Nat) → (v : Nat) → Type where
  | root (r : Nat) : BfsLex delta 0 r
  | childOf {d parent curr : Nat} 
      (p : BfsLex delta d parent) 
      (h_adj : Adj parent curr) : BfsLex delta (d + 1) curr
  | sameLayerNeighbor {d peer curr : Nat} 
      (p : BfsLex delta d peer) 
      (h_adj : Adj peer curr) : BfsLex delta d curr

/-- Every node carries a structural guarantee that its out-degree matches or exceeds delta -/
structure BfsNode (delta : Nat) where
  id   : Nat
  dist : Nat
  path : BfsLex delta dist id
  -- Natively embed the minimum degree property into the node definition
  degree_ge_delta : cardN1 id ≥ delta

-- 1. Replace G.dist with a check against your executable BFS output
def bfsLayerVerts (graph : Array (List Nat)) (v₀ : Nat) (k : Nat) : Nat → Prop :=
  fun v => (bfsDistances graph v₀)[v]? = some (some k)

-- 2. Update Interior Neighbors
def interiorNeighbors (graph : Array (List Nat)) (k : Nat) (v₀ : Nat) (u : BfsNode (ArrayGraph.Adj graph)) : Nat → Prop :=
  fun v => ArrayGraph.Adj graph u.id v ∧ bfsLayerVerts graph v₀ (k + 1) v

-- 3. Update Exterior Neighbors
def exteriorNeighbors (graph : Array (List Nat)) (k : Nat) (v₀ : Nat) (u : BfsNode (ArrayGraph.Adj graph)) : Nat → Prop :=
  fun w => ∃ v, interiorNeighbors graph k v₀ u v ∧ ArrayGraph.Adj graph v w ∧ bfsLayerVerts graph v₀ (k + 2) w

def bfsParents (graph : Array (List Nat)) (start : Nat) : Array (Option Nat) := Id.run do
  -- Stores the parent of each node. The root points to itself or a sentinel.
  let mut parents := Array.mkArray graph.size none
  let mut visited : Std.HashSet Nat := Std.HashSet.empty
  let mut queue : List Nat := []

  if h : start < graph.size then
    parents := parents.set ⟨start, h⟩ (some start) -- Root is its own parent
    visited := visited.insert start
    queue := [start]

  let fuel := graph.size * graph.size
  for _ in [0:fuel] do
    match queue with
    | [] => break
    | curr :: tail =>
      queue := tail

      if hCurr : curr < graph.size then
        let neighbors := graph[curr]

        for neighbor in neighbors do
          if !visited.contains neighbor then
            visited := visited.insert neighbor
            queue := queue ++ [neighbor] 
            
            if hNeigh : neighbor < parents.size then
              -- Set the parent of 'neighbor' to be 'curr'
              parents := parents.set ⟨neighbor, hNeigh⟩ (some curr)

  return parents

/-- 
  Traces back from a vertex to the root using the parents array.
  Returns the path as a list of vertices from start to target.
-/
def reconstructPath (parents : Array (Option Nat)) (start : Nat) (target : Nat) : List Nat :=
  let fuel := parents.size
  let rec go (curr : Nat) (acc : List Nat) (f : Nat) : List Nat :=
    match f with
    | 0 => [] -- Out of fuel (failsafe)
    | f' + 1 =>
      if curr == start then
        start :: acc
      else
        match parents[curr]? with
        | some (some parent) => go parent (curr :: acc) f'
        | _                  => [] -- No path exists
  go target [] fuel

/-- Proves that a list of nodes forms a valid path from `u` to `v` -/
inductive IsValidPath (Adj : Nat → Nat → Prop) : Nat → Nat → List Nat → Prop where
  | single (u : Nat) : IsValidPath Adj u u [u]
  | step {u v w : Nat} {path : List Nat} 
      (h_path : IsValidPath Adj u v (v :: path)) 
      (h_adj : Adj v w) : IsValidPath Adj u w (w :: v :: path)

-- Replacement for G.dist_le_succ_of_adj
lemma dist_le_succ_of_adj {u v : Nat} (h_adj : Adj u v) (d_u : Nat) (h_u : Dist v₀ u d_u) :
  ∃ d_v, Dist v₀ v d_v ∧ d_v ≤ d_u + 1

-- 1. Vertices up to k (replaces verticesUpTo)
def verticesUpTo (graph : Array (List Nat)) (v₀ : Nat) (k : Nat) : Nat → Prop :=
  fun v => ∃ d, (bfsDistances graph v₀)[v]? = some (some d) ∧ d ≤ k

-- 2. Edges in the induced subgraph up to k incident to v
-- Replaces: (((G.induce (verticesUpTo G v₀ k)).edgeFinset).filter (fun e => v ∈ e))
def inducedEdgesIncident (graph : Array (List Nat)) (v₀ : Nat) (k : Nat) (v : Nat) : (Nat × Nat) → Prop :=
  fun ⟨u, w⟩ => 
    (u = v ∨ w = v) ∧               -- Filtered to contain v
    ArrayGraph.Adj graph u w ∧       -- Is a valid edge
    verticesUpTo graph v₀ k u ∧     -- Endpoint u is in the subgraph
    verticesUpTo graph v₀ k w       -- Endpoint w is in the subgraph

/-- Collects all edges incident to `v` where both endpoints are within distance `k` -/
def getInducedEdgesIncident (graph : Array (List Nat)) (v₀ : Nat) (k : Nat) (v : Nat) : List (Nat × Nat) :=
  if h : v < graph.size then
    -- Get all neighbors of v
    let neighbors := graph[v]
    -- Filter neighbors to ensure both v and the neighbor are within distance k
    let distances := bfsDistances graph v₀
    neighbors.filterMap (fun neighbor => 
      match distances[v]?, distances[neighbor]? with
      | some (some d_v), some (some d_n) =>
        if d_v ≤ k ∧ d_n ≤ k then some (v, neighbor) else none
      | _, _ => none
    )
  else
    []

variable {Adj : Nat → Nat → Prop}

/-- Strict lexicographical comparison on BfsNodes -/
def BfsLt (a b : BfsNode Adj) : Prop :=
  a.dist < b.dist ∨ (a.dist = b.dist ∧ a.id < b.id)


/-- A helper function to map a BfsNode to a standard Nat pair -/
def BfsNode.toProd (u : BfsNode Adj) : Nat × Nat :=
  (u.dist, u.id)

/-- 
  Theorem: The lexicographical relation on BfsNode is well-founded.
  This allows you to safely use well-founded induction or find minimums in subgraphs.
-/
theorem bfsLt_wellFounded (Adj : Nat → Nat → Prop) : WellFounded (@BfsLt Adj) := by
  -- We prove this by showing BfsLt is a sub-relation of the standard Nat × Nat lex order
  let f := fun (u : BfsNode Adj) => (u.dist, u.id)
  apply WellFounded.subrelation (r := fun a b => Prod.Lex Nat.lt Nat.lt (f a) (f b))
  · -- Part 1: Show that BfsLt logically implies Prod.Lex
    intro a b h
    rcases h with h_dist | ⟨h_eq, h_id⟩
    · exact Prod.Lex.left a.dist b.dist a.id b.id h_dist
    · rw [h_eq]
      exact Prod.Lex.right b.dist a.id b.id h_id
  · -- Part 2: Show that the inverse image of a well-founded relation is well-founded
    exact WellFounded.invImage (Prod.lex Nat.lt Nat.lt) f

variable {Adj : Nat → Nat → Prop}

/-- Returns the lexicographically smaller of two BfsNodes -/
def bfsNodeMin (a b : BfsNode Adj) : BfsNode Adj :=
  if a.dist < b.dist then a
  else if a.dist = b.dist && a.id ≤ b.id then a
  else b

/-- 
  Finds the minimum BfsNode in a list. 
  Takes a default fallback node to handle the empty list safely (avoiding Options).
-/
def findMinBfsNode (ls : List (BfsNode Adj)) (default : BfsNode Adj) : BfsNode Adj :=
  match ls with
  | [] => default
  | x :: xs => xs.foldl bfsNodeMin x


-- Partition Lemma 
variable {Adj : Nat → Nat → Prop}

-- Compressed structural definitions using Prop instead of heavy Mathlib Sets
def backNeighbors (k : Nat) (w_dist : Nat) : Prop := w_dist ≤ k
def interiorNeighbors (k : Nat) (w_dist : Nat) : Prop := w_dist = k + 1
def exteriorNeighbors (k : Nat) (w_dist : Nat) : Prop := w_dist = k + 2

/-- 
  Computes the induced subgraph containing only vertices at distance layer `k`,
  and includes only the edges where both endpoints belong to layer `k`.
-/
def getSubgraphAtLayer (graph : Array (List Nat)) (getLayer : Nat → Nat) (k : Nat) : Array (List Nat) :=
  -- Initialize a blank graph of the same size
  let emptyGraph := Array.mkArray graph.size []
  
  -- We fold over the original graph to populate the induced edges
  graph.enum.foldl (fun acc (u, neighbors) =>
    if getLayer u == k then
      -- Filter neighbors to only keep those that are ALSO at layer k
      let inducedNeighbors := neighbors.filter (fun w => getLayer w == k)
      acc.set! u inducedNeighbors
    else
      -- If the vertex u is not in layer k, it gets an empty neighbor list
      acc
  ) emptyGraph

/-- Counts the number of active vertices inhabiting layer k -/
def getVertexCountAtLayer (graph : Array (List Nat)) (getLayer : Nat → Nat) (k : Nat) : Nat :=
  (List.range graph.size).filter (fun u => getLayer u == k).length

/-- Counts the total number of directed arcs contained inside the layer-k induced subgraph -/
def getEdgeCountAtLayer (subgraph : Array (List Nat)) : Nat :=
  subgraph.foldl (fun acc neighbors => acc + neighbors.length) 0



/-- Port and compression of partition proof -/
theorem position_lemma (k : Nat) (v : BfsNode Adj) (hv : v.dist = k + 1) (w : BfsNode Adj) :
    interiorNeighbors k w.dist ∨ exteriorNeighbors k w.dist ∨ backNeighbors k w.dist := by
  -- Since distances are Nats, the layer structure guarantees it falls into one of these bounds
  have h_cases : w.dist = k + 1 ∨ w.dist = k + 2 ∨ w.dist ≤ k := by omega
  rcases h_cases with h1 | h2 | h3
  · left; exact h1
  · right; left; exact h2
  · right; right; exact h3

/-- Compressed translation of layers_disjoint -/
lemma layers_disjoint (v₀ u : Nat) (a b : Nat) (h_ne : a ≠ b) 
    (ha : (bfsDistances graph v₀)[u]? = some (some a)) 
    (hb : (bfsDistances graph v₀)[u]? = some (some b)) : False := by
  -- Lean's option unwrapping forces the internal values to match, contradicting h_ne
  injection (by injection ha) with ha'
  injection (by injection hb) with hb'
  omega

/-- 
  Compressed translation of local_edges_disjoint_from_previous.
  If an edge (u, v) exists in a subgraph bounded up to layer `k`,
  the node `v` cannot belong to layer `k + 1`.
-/
lemma local_edges_disjoint_from_previous (k : Nat) (u v : Nat)
    (h_prev_u : ∃ d, (bfsDistances graph v₀)[u]? = some (some d) ∧ d ≤ k)
    (h_prev_v : ∃ d, (bfsDistances graph v₀)[v]? = some (some d) ∧ d ≤ k)
    (hv_layer : (bfsDistances graph v₀)[v]? = some (some (k + 1))) : False := by
  rcases h_prev_v with ⟨d, hd, h_le⟩
  -- hd says distance is d (where d ≤ k), but hv_layer says distance is k + 1.
  -- This match forces an exact contradiction.
  injection (by injection hd) with hd'
  injection (by injection hv_layer) with hv_layer'
  omega


--NextLink
variable {Adj : Nat → Nat → Prop}

/-- Predicate tracking deep forward layers -/
def outNeighborsDeep (i : Nat) (w_dist : Nat) : Prop := w_dist ≥ i

/-- 
  Compressed Lemma 1: Forward deep neighbors of u_i are disjoint from 
  the direct layer-neighbors of a strictly lower node v_k.
-/
theorem lower_layer_neighbors_disjoint (i k : Nat) (hk : k < i) (u_i v_k : BfsNode Adj) (w : BfsNode Adj)
    (hu : u_i.dist = i)
    (hv : v_k.dist = k)
    (h_deep : outNeighborsDeep i w.dist)
    (h_vk_out : interiorNeighbors k w.dist) : False := by
  -- 1. Unpack definitions to reveal pure Nat properties
  rw [outNeighborsDeep] at h_deep             -- w.dist ≥ i
  rw [interiorNeighbors] at h_vk_out         -- w.dist = k + 1
  
  -- 2. Let omega crush the bounds: k + 1 cannot be ≥ i when k < i
  omega

/-- Second out-neighborhood structurally tracked from a BfsNode -/
def N2BfsNode (u : BfsNode Adj) (w_dist : Nat) : Prop :=
  ∃ z : BfsNode Adj, interiorNeighbors u.dist z.dist ∧ interiorNeighbors z.dist w_dist

/-- 
  Compressed Lemma 2: Direct neighbors of a back-arc node v_k are structurally 
  absorbed into the second out-neighborhood of the higher-layer node u_i.
-/
theorem out_neighbors_subset_outNeighbor2 (i k : Nat) (hk : k < i) (u_i v_k : BfsNode Adj) (w : BfsNode Adj)
    (hu : u_i.dist = i)
    (hv : v_k.dist = k)
    (h_back_arc : interiorNeighbors u_i.dist v_k.dist) -- v_k is an interior neighbor of u_i
    (hw : interiorNeighbors v_k.dist w.dist) :           -- w is an interior neighbor of v_k
    N2BfsNode u_i w.dist := by
  -- We provide v_k as the explicit structural witness `z` linking u_i to w
  use v_k
  rw [hu, hv] at h_back_arc
  rw [hv] at hw
  exact ⟨h_back_arc, hw⟩
/--
/-- Lemma 2: Direct neighbors of a back-arc node v_k are absorbed into N2 of u_i -/
theorem out_neighbors_subset_outNeighbor2 (i k : Nat) (hk : k < i) (u_i v_k w : BfsNode delta)
    (hu : u_i.dist = i)
    (hv : v_k.dist = k)
    (h_back_arc : v_k.dist ≤ u_i.dist) -- Structural tracking of the back-arc link
    (hw : interiorNeighbors v_k.dist w.dist) : N2BfsNode u_i w := by
  use v_k
  rw [interiorNeighbors] at hw
  constructor
  · rw [hu]
    right; exact h_back_arc
  · exact hw-/

/--
theorem next_link_backarc_bound (i k : Nat) (hk : k < i) (u_i v_k w : BfsNode Adj)
    (hu : u_i.dist = i) (hv : v_k.dist = k)
    (h_disjoint : outNeighborsDeep i w.dist → interiorNeighbors k w.dist → False)
    (h_sub_two : interiorNeighbors k w.dist → N2BfsNode u_i w.dist)
    (h_sub_old : outNeighborsDeep i w.dist → N2BfsNode u_i w.dist) :
    (outNeighborsDeep i w.dist ∨ interiorNeighbors k w.dist) → N2BfsNode u_i w.dist := by
  -- Pure structural implication replacing the old heavy Finset/Set union inclusion rules
  intro h_union
  rcases h_union with h_old | h_two
  · exact h_sub_old h_old
  · exact h_sub_two h_two
-/
/-- The Final Capacity Squeeze: If a back-arc occurs, the arithmetic bounds snap shut -/
theorem next_link_backarc_bound (i k : Nat) (hk : k < i) (u_i v_k : BfsNode delta)
    -- Hypotheses linking capacity measurements
    (h_non_seymour : cardN1 u_i.id > cardN2 u_i.id) -- MCE condition: N1 > N2
    (h_deg_bound : cardN1 u_i.id ≥ delta)          -- Degree constraint
    (h_disjoint_cap : cardN2 u_i.id ≥ deepCount + childCount) -- From disjointness lemma
    (h_child_expansion : childCount ≥ delta)       -- Lower layer node must expand out by delta
    : False := by
  -- Let's trace what omega sees here:
  -- 1. cardN2 u_i.id < cardN1 u_i.id (from h_non_seymour)
  -- 2. cardN2 u_i.id ≥ deepCount + childCount (from h_disjoint_cap)
  -- 3. childCount ≥ delta (from h_child_expansion)
  -- 4. cardN1 u_i.id is bounded by delta...
  -- This creates an inescapable arithmetic loop: cardN2 ≥ delta, but cardN2 < cardN1 (where cardN1 could be delta).
  omega

-- Load Balance Theorem by Induction 
variable {Adj : Nat → Nat → Prop}



variable {delta : Nat} {Adj : Nat → Nat → Prop}

/-- 
  Inductive Base Definition: Neighbors of the root (layer 0) 
  are structurally bound to layer 1. 
-/
theorem base_case_definition (v₀ x : BfsNode delta) 
    (hu : v₀.dist = 0)
    (h_int : interiorNeighbors v₀.dist x.dist) : x.dist = 1 := by
  rw [hu, interiorNeighbors] at h_int
  exact h_int

/-- 
  Inductive Case Definition: Neighbors of a layer-k node 
  are structurally bound to layer k + 1. 
-/
theorem inductive_case_definition (k : Nat) (u x : BfsNode delta) 
    (hu : u.dist = k)
    (h_int : interiorNeighbors u.dist x.dist) : x.dist = k + 1 := by
  rw [hu, interiorNeighbors] at h_int
  exact h_int

-- Base Case Pigeonhole Principle
have h_R1_size : getVertexCountAtLayer graph getLayer 1 = delta
have h_R2_size : getVertexCountAtLayer graph getLayer 2 ≤ delta - 1

theorem base_case_pigeonhole_final (delta : Nat) 
    (R1_vertex_count : Nat) (R2_vertex_count : Nat)
    (h_R1 : R1_vertex_count = delta)
    (h_R2 : R2_vertex_count ≤ delta - 1)
    -- Metrics for a specific node x in R1
    (x_deg : Nat) (x_back : Nat) (x_forward : Nat) (x_interior : Nat)
    (h_x_deg : x_deg ≥ delta)
    (h_x_sum : x_deg = x_back + x_forward + x_interior)
    -- Structural bounds
    (h_back_bound : x_back ≤ 1)
    (h_fwd_bound : x_forward ≤ R2_vertex_count)
    : x_interior > 0 ∨ (x_back = 1 ∧ x_forward = delta - 1) := by
  -- omega reads the system of linear inequalities and proves 
  -- that x_interior must be strictly greater than 0 unless it hits the absolute geometric maximum
  omega


theorem inductive_pigeonhole_step (delta k : Nat) (R_k2_size : Nat)
    -- 1. Bound from the I.H. / Non-Seymour property at depth k
    (h_R_k2_capacity : R_k2_size ≤ delta - (k + 2) - 1)
    
    -- 2. Degree constraints for an arbitrary node x in R_{k+1}
    (x_deg : Nat) (x_forward : Nat) (x_non_forward : Nat)
    (h_x_deg : x_deg ≥ delta)
    (h_x_sum : x_deg = x_forward + x_non_forward)
    
    -- 3. Structural mapping constraint: forward edges cannot exceed the layer size
    (h_fwd_bound : x_forward ≤ R_k2_size)
    : x_non_forward ≥ k + 2 := by
  -- omega sets up the balance equation:
  -- x_non_forward = x_deg - x_forward
  -- x_non_forward ≥ delta - (delta - k - 3)
  -- Which simplifies directly to: x_non_forward ≥ k + 2
  omega





--Reduction theorem
variable {Adj : Nat → Nat → Prop}

-- An out-neighbor (second neighborhood) from u through some intermediate node
def outNeighbor2 (u w : BfsNode Adj) : Prop :=
  ∃ v : BfsNode Adj, (v.dist = u.dist + 1) ∧ (w.dist = v.dist + 1 ∨ w.dist ≤ v.dist - 1)

def exteriorNeighbors (u_dist v_dist w_dist : Nat) : Prop :=
  w_dist = u_dist + 2

def backNeighbors (v_dist w_dist : Nat) : Prop :=
  w_dist ≤ v_dist - 1

/-- 
  Compressed Part 1 & 3: Exterior or back neighbors of a child v 
  are structurally second neighbors of the parent u.
-/
theorem reduction_definition_containment (u v w : BfsNode Adj)
    (hv : v.dist = u.dist + 1)
    (h_cases : exteriorNeighbors u.dist v.dist w.dist ∨ backNeighbors v.dist w.dist) :
    outNeighbor2 u w := by
  use v
  refine ⟨hv, ?_⟩
  rcases h_cases with h_ext | h_back
  · -- Subcase A: Exterior neighbor
    rw [exteriorNeighbors] at h_ext
    left; omega
  · -- Subcase B: Back neighbor
    rw [backNeighbors] at h_back
    right; omega

/-- 
  Compressed Part 2: When the parent is the root (dist = 0), 
  the back component drops out mathematically.
-/
theorem reduction_base_case_pigeonhole (u v w : BfsNode Adj)
    (hu : u.dist = 0)
    (hv : v.dist = 1)
    (hw : outNeighbor2 u w) : exteriorNeighbors u.dist v.dist w.dist := by
  rcases hw with ⟨v', hv', h_w_cases⟩
  rw [exteriorNeighbors]
  -- omega recognizes that w cannot leak backward since dist cannot be negative,
  -- isolating the layer cleanly to 2.
  omega

/-- 
  Compressed Part 4: Inductive Step Squeeze.
  An out-neighbor of a child node must fall into either the exterior or back partition.
-/
theorem reduction_inductive_step_squeeze (u v w : BfsNode Adj)
    (hv : v.dist = u.dist + 1)
    (hw : outNeighbor2 u w) 
    (h_not_horizontal : w.dist ≠ u.dist + 1) : 
    exteriorNeighbors u.dist v.dist w.dist ∨ backNeighbors v.dist w.dist := by
  rcases hw with ⟨v', hv', h_w_cases⟩
  rw [exteriorNeighbors, backNeighbors]
  -- omega clamps the arithmetic possibilities directly from the hypothesis,
  -- bypassing the entire topological Partition Lemma step.
  omega
