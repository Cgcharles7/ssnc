def ArrayGraph.Adj (graph : Array (List Nat)) (u v : Nat) : Prop :=
  ∃ h : u < graph.size, v ∈ graph[u]

inductive BfsLex (Adj : Nat → Nat → Prop) : (d : Nat) → (v : Nat) → Type where
  | root (r : Nat) : BfsLex Adj 0 r
  | childOf {d parent curr : Nat} 
      (p : BfsLex Adj d parent) 
      (h_adj : Adj parent curr) : BfsLex Adj (d + 1) curr
  | sameLayerNeighbor {d peer curr : Nat} 
      (p : BfsLex Adj d peer) 
      (h_adj : Adj peer curr) : BfsLex Adj d curr

structure BfsNode (Adj : Nat → Nat → Prop) where
  id   : Nat
  dist : Nat
  path : BfsLex Adj dist id

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

