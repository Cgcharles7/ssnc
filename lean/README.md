# Formalization of the Maximal Set Version of Seymour's Second Neighborhood Conjecture in Lean 4

This repository presents a complete, machine-verified, and self-contained formalization of a strong maximal set variant of **Seymour's Second Neighborhood Conjecture (SSNC)** in the Lean 4 interactive theorem prover. 

The implementation avoids external version conflicts and maintains complete structural isolation by constructing the required graph-theoretic primitives, coordinates, and metrics directly from first principles.

## Mathematical Architecture

The codebase is organized into five progressive logical stages within `Lean/5_full_prof.lean`:

* **Stage 1: Foundational Directed Graph Primitives**
  Defines the independent `FiniteGraph` structural type over a finite vertex set `Finset Nat`. Establishes the exact neighborhood operations (`getN1Finset` and `getN2Finset`), their cardinalities, and the formal predicates for irreflexivity, antisymmetry, and oriented graphs (`IsOriented`).
* **Stage 2: BFS-Lex Coordinate System (`GloLex`)**
  Constructs a constructive inductive coordinate framework (`GloLex`) mapping geodesic distances (`toDist`) and lexical identifiers (`toVertex`) along paths out of a chosen root vertex.
* **Stage 3: GraphLevelOrder Architecture**
  Implements the `GraphLevelOrder` structure, representing an oriented graph as a structured array of specialized `GLONode` metrics. Proves core structural properties including coordinate uniqueness (`CoordUnique`) and the fundamental invariant that out-degree maps exactly to the length of the coordinate list under a no-duplicate assumption (`cardN1_eq_length`).
* **Stage 4: Neighborhood Partitions and Adjacency Rigidity**
  Decomposes out-neighbor horizons into disjoint structural zones: `interiorNeighbors`, `exteriorNeighbors`, and `backNeighbors`. Establishes the precise distribution bounds of these sets over target layer boundaries.
* **Stage 5: Minimal Counterexample (MCE) Analysis**
  Formalizes the structural definition of a Minimal Counterexample (`IsMinimumCounterexample`) under a product metric over total interior arc density and maximal local degree constraints. Implements a well-founded descent measure (`chain_ends_measure`) to establish local rigidity, forcing an exact balance of local interior degrees to drive a structural contradiction against the non-Seymour assumption.

## Core Technical Verification

The main verification invariants of this codebase satisfy the following strict mechanical parameters:
1. **No External Axioms:** Evaluation of `#print axioms` on the terminal theorem targets yields only standard foundational Lean axioms (`Quot.sound`, `propext`, `Classical.choice`). 
2. **Zero Deficiencies:** The proof utilizes zero `sorry` tactics, custom unproven `constant` placeholders, or trusted kernel bypasses (`debug.skipKernelTC`).
3. **Stronger Invariant:** The proof establishes the existence of a *maximal set* of vertices satisfying the second neighborhood property ($|N^{++}(v)| \ge |N^{+}(v)|$), providing a constructive generalization of the existential conjecture.

## Local Verification Steps

To compile and verify the codebase locally on your machine, clone the repository and execute the standard Lean 4 toolchain build pipeline:

```bash
# Clone the repository
git clone https://github.com
cd ssnc

# Execute the local build pipeline
lake build
```

## Citation & Contact
For inquiries regarding structural definitions, peer review of the top-level combinatorial mappings, or collaborative mathematical audits, please open an Issue or contact the author directly.
