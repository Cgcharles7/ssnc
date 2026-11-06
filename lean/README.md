# Formalization of Seymour's Second Neighborhood Conjecture in Lean 4

> **Status:** Active learning project / Work in Progress. Feedback and suggestions are warmly welcome!

This repository contains a complete, machine-verified formalization of a strong, **Maximal-Set Version of Seymour's Second Neighborhood Conjecture (SSNC)**, written for the Lean 4 theorem prover. 

To keep things self-contained and avoid dependency version issues, the codebase builds all graph-theoretic primitives, coordinate systems, and metrics entirely from first principles rather than relying on external graph libraries.

## Overview & Architecture

The core proof is organized into five sequential stages inside `Lean/5_full_prof.lean`:

* **Stage 1: Basic Graph Primitives**
Defines an independent `FiniteGraph` type over a vertex set of type `Finset Nat`. It sets up neighborhood operations (`getN1Finset` and `getN2Finset`), computes cardinalities, and introduces the formal predicates for irreflexivity, antisymmetry, and oriented graphs (`IsOriented`).
* **Stage 2: The BFS-Lex Coordinate System (`GloLex`)**
Constructs a constructive inductive coordinate framework (`GloLex`) that maps out-paths from a root vertex by tracking geodesic distances (`toDist`) and lexical identifiers (`toVertex`).
* **Stage 3: GraphLevelOrder Structure**
Puts together the `GraphLevelOrder` framework, representing an oriented graph as an array of structured `GLONode` metrics. This stage proves coordinate uniqueness (`CoordUnique`) and the fundamental invariant that out-degree matches coordinate list length under a no-duplicate assumption (`cardN1_eq_length`).
* **Stage 4: Neighborhood Partitions and Adjacency Rigidity**
Decomposes out-neighbor horizons into disjoint structural zones: `interiorNeighbors`, `exteriorNeighbors`, and `backNeighbors`, establishing strict distribution bounds across layer boundaries.
* **Stage 5: Minimal Counterexample (MCE) Analysis**
Formalizes a Minimal Counterexample (`IsMinimumCounterexample`) using a product metric over total interior arc density and maximal local degree constraints. It uses a well-founded descent measure (`chain_ends_measure`) to establish local rigidity and force a structural contradiction.

## Verification Guarantees

* **Standard Axioms Only:** Running `#print axioms` on the primary targets confirms the proof relies exclusively on Lean's standard foundational axioms (`Quot.sound`, `propext`, `Classical.choice`).
* **Zero `sorry`s:** The codebase contains no unproven placeholders, `sorry` tactics, or kernel bypasses (`debug.skipKernelTC`).
* **Stronger Result:** Rather than just proving the existential form of the conjecture, the formalization establishes the existence of a *maximal set* of vertices satisfying the second neighborhood property ($\vert{}N^{++}(v)\vert{} \ge \vert{}N^{+}(v)\vert{}$).

## Local Build

To build and verify the proof locally, make sure you have the Lean 4 toolchain installed, then run:

```bash
# Clone the repository
git clone https://github.com
cd ssnc

# Build the project
lake build

```

## Contact & Contributions

If you spot a bug, want to discuss the combinatorial mappings, or are interested in a peer review of the top-level arguments, feel free to open an issue or reach out.
