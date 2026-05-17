# A Constructive Proof of the Seymour Second Neighborhood Conjecture via Graph Level Order (GLO)

**[Live Seymour Proof Engine (dgsquare.htm)](https://cgcharles7.github.io/SeymourConjecture/javascript_files/dgsquare.htm)** 

* **Author:** Charles N. Glover (Independent Researcher)
* **Core Paper Reference:** *"A Minimum Counterexample Proof of the Seymour Second Neighborhood Conjecture via the Graph Level Order"* ([Read on alphaXiv](https://www.alphaxiv.org/abs/2501.00614)).
* **License:** [MIT License](LICENSE)

---

## Purpose & Audience

This repository provides an open-source, computationally auditable verification environment for a constructive proof of **Seymour's Second Neighborhood Conjecture (SSNC)**. 

### A 20+ Year Journey in Silence 
The code in this repository was created over my mathematical journey. I love this problem not only because of it is simple to state, but because I used it to introduce me to many graph and mathematical algorithms. When I started working on the problem, I didn't know how to read math papers. I literally sent an expert a sketch of my idea thinking I solved it trivially. I didn't. But even back then I could code. I began this site, to see what I was missing and what could be corrected. 


### Why This Repository Exists
The graph theory community approaches the SSNC through many existential methods. They have used random graphs and Constraint Satisfaction Problems (CSPs) most recently. These both assert the existence of a Seymour vertex without explaining why. Computer-assisted approaches generally imply brute-force approach. Again this fails to uncover the structural truth.

This project bridges the gap between these two worlds. It is built for graph theorists, discrete mathematicians, theoretical computer scientists, and anyone interested in the Seymour Second Neighborhood Conjecture and the underlying structure of the problem.

---

## Algorithmic Overview: How the Conjecture Was Solved

The Seymour Second Neighborhood Conjecture states that every oriented graph contains at least one vertex whose second out-neighborhood is at least as large as its first out-neighborhood ($|N^2(v)| \ge |N^1(v)|$). 

Rather than testing individual graphs, this framework **tames the infinite search space by classifying all oriented graphs by their minimum out-degree ($\delta$)**. 

### 1. Establishing the Coordinate System (The Well-Ordering)
In a locally finite infinite graph (or a standard finite graph), the minimum degree node has a finite degree. By anchoring our analysis at this minimum out-degree node, we execute a Breadth-First Search (BFS) decomposition paired with a lexicographical ordering. 

This establishes a coordinate system or a **well-ordering** on the graph's vertices. It maps every node to an exact spatial coordinate: 
$$\text{Node Coordinate} = (\text{distance}, \text{lex\_node\_id})$$

### 2. Operating in the Dual Space: Vertex Packing
Instead of passively searching for a needle-in-a-haystack Seymour vertex, this framework operates entirely within the **dual space**. We systematically **"pack" non-Seymour vertices** inside a strict Minimum Counterexample (MCE) environment until the structural boundaries collapse and a valid Seymour vertex is forced to emerge.

### 3. "Kicking the Can Down the Road": Forward-Facing Transitive Triangles
In traditional literature, transitive triangles are often viewed negatively as structural noise. However, inside the dual optimization space, they possess a powerful feature: **they allow parent vertices to pass the Seymour property onto their children, enabling the parents to remain non-Seymour.**

* Parents use these triangles to "kick the can down the road" to their children.
* Children must "agree" to absorb this property. If they refuse, the game immediately ends because a Seymour vertex has been found. 
* To prolong the existence of the counterexample, both parents and children are structurally incentivized to keep passing this property forward as long as possible.

### 4. The Set Cover Collapse, Back Arcs, and Layer Decay
We prove that these forward-facing transitive triangles must form a **minimum set cover** over the parent's first out-neighborhood ($N^1(u)$). This structural requirement forces specific topological properties:
* **Forced Cycles:** The minimum set cover produces a cycle among the children, forcing each child to have an out-degree of at least $1$.
* **Edge Redundancy:** Because it is a *minimum* set cover, any child vertex with an out-degree greater than $1$ possesses an unnecessary edge that fails to help reduce the size of the second neighborhood. 
* **Neighborhood Shrinkage:** Consequently, the children (which must have an out-degree of at least $\delta$) can afford one less out-degree in the second neighborhood. This forces the second neighborhood to shrink below the size of the first neighborhood ($|N^2(u)| < |N^1(u)|$). This, mathematically defines the parent $u$ as a non-Seymour vertex.
* **The Elimination of Back Arcs:** While forward tree arcs discover new nodes for inspection, back arcs merely loop back to already inspected nodes. We demonstrate that any counterexample containing a back arc can be systematically reduced into a smaller structural instance by replacing it with a forward arc. Thus, **back arcs cannot exist within an MCE.**

This structural purge forces a state of absolute **$\delta$-regularity overall and $k$-regularity at distance $k$**. Every neighborhood layer is rendered Eulerian, composed entirely of disjoint cycles.

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

