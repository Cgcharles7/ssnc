# A Constructive Proof of the Seymour Second Neighborhood Conjecture via the Graph Level Order (GLOVER)


* **Author:** Charles N. Glover
* **Core Paper Reference:** *"A Minimum Counterexample Proof of the Seymour Second Neighborhood Conjecture via the Graph Level Order"* ([Read on alphaXiv](https://www.alphaxiv.org/abs/2501.00614)).
* **License:** [MIT License](LICENSE)

---

## Purpose & Audience
This repository provides an open-source, computationally auditable verification environment for a constructive proof of **A Maximal Set Version of the Seymour Second Neighborhood Conjecture (SSNC).**

### A 20+ Year Journey in Silence 
The code in this repository was created over my mathematical journey. I love this problem not only because of it is simple to state, but because I used it to introduce me to many graph and mathematical algorithms. When I started working on the problem, I didn't know how to read math papers. I literally sent an expert a sketch of my idea (Breadth First Search) thinking I solved the problem trivially. It didn't. But even back then I could code. So I kept chipping away at the problem. I began writing programs to see what I was missing and what could be corrected.

### Why This Repository Exists
The graph theory and mathematical community as a whole approaches SSNC through mostly existential methods. They have used random graphs and Constraint Satisfaction Problems (CSPs) most recently. These both assert the existence of a Seymour vertex without explaining why. Computer-assisted approaches generally imply a brute-force-like approach, typically through bounding a polyhedron. Again, this fails to uncover the structural truth.

The goal of this is to bridge the gap between the worlds of mathematics and computer science. It is built for graph theorists, discrete mathematicians, theoretical computer scientists, and anyone interested in finding Seymoour vertices. Other researchers can prove they exist. My algorithm, through the Breadth First Search technique and Minimum Counterexamples, can find a path to those vertices.

---

## Algorithmic Overview

The Seymour Second Neighborhood Conjecture states that every oriented graph (a directed graph without bi-directional edges or loops) contains at least one vertex whose second out-neighborhood is at least as large as its first out-neighborhood ($|N^2(v)| \ge |N^1(v)|$). 

Rather than testing individual graphs or searching for a Seymour vertex, this framework **classifies all oriented graphs by their minimum out-degree (δ) in the form of a minimum counterexample (MCE)**.

### 1. Establishing the Coordinate System (The Well-Ordering)
In a standard finite graph, the minimum out-degree node has a finite degree. We execute a Breadth-First Search (BFS) traversal paired with a lexicographical ordering. This gives every node in the graph a **unique coordinate pair (distance, lexID)** within each BFS layer. The distance is respective to the minimum out-degree node, and the lexID is within the perspective local neighborhood. This establishes a coordinate system and a **well-ordering** on the graph's vertices.

### 2. Operating in the Dual Space: Vertex Packing
Instead of searching for a needle-in-a-haystack Seymour vertex, this framework operates entirely within the **dual space**. It systematically **"pack" non-Seymour vertices** inside a strict MCE environment until Seymour vertices are forced to emerge.

### 3. Forward-Facing Transitive Triangles
In traditional literature, all transitive triangles are always grouped into the same bucked, and generally always included or excluded. However, inside this dual space, forward facing transitive triangles possess a powerful feature: **they allow parent vertices to become non-Seymour, while at the same time passing the Seymour test onto their children.**

* Parents use these triangles to "kick the can down the road" to their children.
* Children must "agree" to absorb this property. If they refuse, the game immediately ends because a Seymour vertex has been found. 
* To prolong the existence of the counterexample, both parents and children are structurally incentivized to keep passing this property forward as long as possible.

### 4. The Set Cover Collapse, Back Arcs, and Layer Decay
We prove that these forward-facing transitive triangles must form a **minimum set cover** over the parent's first out-neighborhood ($N^1(u)$). This structural requirement forces specific topological properties:

* **Forced Cycles:** The minimum set cover produces a cycle among the children, forcing each child to have an out-degree of at least $1$.
* **Neighborhood Shrinkage**: In an MCE environment, all nodes must be non-Seymour. This forces the second neighborhood of every parent node to be smaller than the first neighborhood (|N^2(u)|<|N^1(u)|). To accomplish this, child nodes (in the next BFS layer, i.e. the first neighborhood of the parent) must partition their out-neighbors into interior neighbors and exterior neighbors. Interior neighbors intersect with the parent, whereas exterior neighbors are second neighbors of the parent. Interior neighbors prevent the parent from becoming Seymour. 
* **Minimum Out-Degree Requirement**: The lower bounds on this model are enforced by the minimum out-degree constraint. This forces every node to have out-degree at least $\delta$. The non-Seymour requirement combined with child nodes producing less than $\delta$ exterior nodes means that they must connect to more interior nodes (or back arcs) to keep the parents non-Seymour.
* **Minimum Counterexample**: The primary definition of MCE is minimizing the number of interior arcs (also known as neighborhood density). This places an upper bound on these interior neighbors. This forces the BFS layers to decrease at a consistent rate of 1. 
* **Neighborhood Shrinkage:** Consequently, the children can afford one less out-degree in the second neighborhood. This forces the second neighborhood to shrink below the size of the first neighborhood ($|N^2(u)| < |N^1(u)|$). This, mathematically defines the parent $u$ as a non-Seymour vertex.
* **The Elimination of Back Arcs:** While forward tree arcs discover new nodes for inspection, back arcs merely loop back to already inspected nodes. We demonstrate that both disconnected and connected back arcs are impossible in an MCE oriented graph. 

This structural purge forces a state of absolute **$\delta$-regularity overall as well as interior degree regularity**. Every neighborhood layer is rendered Eulerian by adding a second metric to the MCE that minimizes the max total interior degree. This makes the optimal MCEs consist of graphs that composed entirely of disjoint cycles.

As these neighborhood layers move further away from the root minimum-degree node, they are forced to become increasingly dense. To keep nodes non-Seymour at distance $k+1$, you must pack $k$ disjoint cycles into the neighborhood at distance $k$. Because layer capacity decays linearly ($|R_k| \le \delta - k + 1$), it eventually collides with the quadratic density demands of the binomial formula ($y = x^2$). The graph enters an unsustainable **Collapse Zone**, breaking the counterexample and forcing a Seymour vertex into existence.

---

## 💻 Codebase Architectures & Live Engines

To accommodate different facets of this proof, the repository is split into independent, specialized runtime implementations:

### 🐍 The Python 3.10+ Implementation (Big Data & Heavy Verification)
The Python engine (located in `/python/`) is built for rigorous, high-throughput mathematical validation. It leverages scientific computing libraries to run large-scale matrix computations, evaluating heavy graph data across dense matrices to verify that the layer-decay boundaries hold true across massive structural instances.

### 🟨 The Client-Side Web Engines (Visual & Interactive Topologies)
Located within the `/javascript_engines/` directory, these self-contained web applications translate abstract geometric structures into immediate, browser-based visual feedback.

#### 1. Core Proof Demonstration: `dgsquare.htm`
This file shows the Seymour Second Neighborhood Conjecture core algorithm in action. It allows you to watch the BFS-lexicographical coordinate system process structural partitions step-by-step, showing how the "can gets kicked down the road" and verifying exactly where the set-cover constraints force an MCE collapse.


While the algorithmic visualizations are stable and testable inside the application, the accompanying formal mathematical manuscripts for these specific results are currently undergoing final revisions. This file is provided openly to allow researchers to interact with the structural data early. Formal citations and paper links will be added here immediately upon submission to arXiv/alphaXiv.

---

## ⚖️ License

This project is licensed under the permissive **MIT License**—see the [LICENSE](LICENSE) file for details. You are free to modify, distribute, and integrate these algorithms into broader graph-theoretic software packages.

---

## ✒️ Citation

```bibtex
@inproceedings{glover2026seymour,
  title={A Minimum Counterexample Proof of the Seymour Second Neighborhood Conjecture via the Graph Level Order},
  author={Glover, Charles N.},
  booktitle={57th Southeastern International Conference on Combinatorics, Graph Theory, and Computing},
  year={2026},
  url={[https://www.alphaxiv.org/abs/2501.00614](https://www.alphaxiv.org/abs/2501.00614)}
}

