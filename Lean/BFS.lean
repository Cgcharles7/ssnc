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

def bfsLex (graph : Array (List Nat)) (start : Nat) : Array String := Id.run do
  -- 1. Call your BFS function to get the array of distances
  let dists := bfsDistances graph start
  
  -- 2. Initialize an array of empty strings matching the graph's size
  let mut ids := Array.mkArray graph.size ""
  
  -- 3. Loop through the nodes and construct the coordinate strings
  for i in [0:graph.size] do
    -- We match on the distance since it is an Option Nat
    let distStr := match dists[i]! with
      | some d => toString d
      | none   => "inf" -- Handle unreachable nodes cleanly
      
    -- Lean 4 uses s!"..." for string interpolation (like f-strings in Python)
    ids := ids.set! i s!"{distStr}_{i}"
    
  return ids
