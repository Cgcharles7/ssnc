import Mathlib

/-
-------------------------------------------------------------------------------
Layout
  1. FiniteGraph and its primitives (neighbourhoods, Seymour predicates)
  2. Graph-level notions that need no root (interior/exterior sets, removeArc, ...)
  3. BFS from an *explicit* root `s` (bfsState / layer / seen) -- the raw machinery
  4. Minimum out-degree vertices
  5. NEGraph: a nonempty graph.  The root is TOTAL, so the BFS layers, distances,
     back/interior/exterior sets, arc counts and the MCE metric are all defined
     with no `Option` anywhere.
  6. Sanity checks and pure arithmetic
-------------------------------------------------------------------------------
-/

structure FiniteGraph (α : Type) [DecidableEq α] where
  vertices : Finset α
  edges : Finset (α × α)
  edge_valid : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices

namespace FiniteGraph

/-! ## 1. Primitives -/

section Defs1
variable {α : Type} [DecidableEq α] (G : FiniteGraph α)

/-- Adjacency predicate derived from the edge finset -/
def Adj (u v : α) : Prop := (u, v) ∈ G.edges
instance (u v : α) : Decidable (G.Adj u v) :=
  inferInstanceAs (Decidable ((u, v) ∈ G.edges))
def N1 (u : α) : Finset α := (G.edges.filter (fun e => e.1 = u)).image (fun e => e.2)
def N2 (u : α) : Finset α := ((G.N1 u).biUnion G.N1).filter (fun w => w ≠ u ∧ w ∉ G.N1 u)
def cardN1 (u : α) : Nat := (G.N1 u).card
def cardN2 (u : α) : Nat := (G.N2 u).card
def getN1Finset (u : α) : Finset α := (G.edges.filter (fun e => e.1 = u)).image (fun e => e.2)
def getN2Finset (u : α) : Finset α :=
  let n1 := getN1Finset G u
  let all_n2 := n1.biUnion (fun v => getN1Finset G v)
  all_n2.filter (fun w => w ≠ u ∧ w ∉ n1)
def isSeymour (u : α) : Bool := cardN2 G u ≥ cardN1 G u
def IsSeymour (u : α) : Prop := G.cardN1 u ≤ G.cardN2 u
def isNonSeymour (u : α) : Bool := cardN2 G u < cardN1 G u
def IsIrreflexive  : Prop := ∀ u ∈ G.vertices, ¬ G.Adj u u
def IsAntisymmetric : Prop := ∀ u v, G.Adj u v → G.Adj v u → u = v
/-- An oriented graph is irreflexive and antisymmetric (no 2-cycles) -/
def IsOriented  : Prop := G.IsIrreflexive ∧ G.IsAntisymmetric
def IsSeymourProp  (u : α) : Prop := cardN1 G u ≤ cardN2 G u
def DNSP (x : α) : Prop := G.cardN2 x < G.cardN1 x

abbrev outNeighbors (u : α) : Finset α := G.N1 u

/-- A counterexample: oriented, nonempty, and every vertex is non-Seymour. -/
def IsCounterexample : Prop :=
  G.IsOriented ∧
  G.vertices.Nonempty ∧
  ∀ x ∈ G.vertices, isNonSeymour G x
end Defs1

section Lemmas1
variable {α : Type} [DecidableEq α] {G : FiniteGraph α}

/-- v is in the finset N1 u exactly when there is an edge u → v -/
@[simp] lemma mem_N1  {u v : α} :
    v ∈ G.N1 u ↔ G.Adj u v := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, he, hb⟩ := Finset.mem_image.1 h
    obtain ⟨he', ha⟩ := Finset.mem_filter.1 he
    simp only at ha hb
    subst ha; subst hb
    exact he'
  · intro h
    exact Finset.mem_image.2 ⟨(u, v), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

/-- w is a second out-neighbor of u when there is a path u → v → w -/
lemma mem_N2  {u w : α} :
    w ∈ G.N2 u ↔ (∃ v, G.Adj u v ∧ G.Adj v w) ∧ w ≠ u ∧ ¬ G.Adj u w := by
  simp [N2, Finset.mem_biUnion, mem_N1]

/-- If there is an edge u → v, both endpoints are vertices of the graph. -/
lemma Adj.mem_vertices {u v : α} (h : G.Adj u v) :
    u ∈ G.vertices ∧ v ∈ G.vertices :=
  G.edge_valid (u, v) h

/-- Out-neighbors of any vertex are vertices. -/
lemma N1_subset_vertices {u w : α} (h : w ∈ G.N1 u) :
    w ∈ G.vertices := (mem_N1.1 h).mem_vertices.2

/-- If w ∈ G.N2 u, then w ∈ G.vertices -/
lemma N2_subset_vertices {u w : α} (h : w ∈ G.N2 u) :
    w ∈ G.vertices := by
  obtain ⟨⟨v, _, hvw⟩, -, -⟩ := mem_N2.1 h
  exact hvw.mem_vertices.2

/-- No vertex is both a first and a second out-neighbor of u. -/
lemma disjoint_N1_N2 (u : α) : Disjoint (G.N1 u) (G.N2 u) :=
  Finset.disjoint_left.2 fun _ h1 h2 => (mem_N2.1 h2).2.2 (mem_N1.1 h1)

lemma N2_not_mem_self {u : α} : u ∉ G.N2 u := fun h =>
  (mem_N2.1 h).2.1 rfl

/-- Connects the two forms of "Seymour at u": the Bool you can compute and the Prop
you can reason about. -/
lemma isSeymour_iff (u : α) :
    G.isSeymour u = true ↔ G.IsSeymourProp u := by
  simp [isSeymour, IsSeymourProp]

lemma node_out_degree_ge_delta
    (u : α)
    (hu_in : u ∈ G.vertices)
    (delta : Nat)
    (h_min : ∀ x ∈ G.vertices, delta ≤ (G.outNeighbors x).card) :
    delta ≤ (G.outNeighbors u).card :=
  h_min u hu_in

lemma DNSP_iff {x : α} : G.DNSP x ↔ G.isNonSeymour x = true := by
  simp [DNSP, isNonSeymour]

lemma DNSP_iff_not_seymour {x : α} : G.DNSP x ↔ ¬ G.IsSeymour x := by
  simp [DNSP, IsSeymour, not_le]

/-- A counterexample is an oriented graph in which every vertex has DNSP. -/
lemma isCounterexample_iff :
    G.IsCounterexample ↔ G.IsOriented ∧ G.vertices.Nonempty ∧ ∀ x ∈ G.vertices, G.DNSP x := by
  unfold IsCounterexample
  constructor <;> rintro ⟨h1, h2, h3⟩ <;>
    exact ⟨h1, h2, fun x hx => by simpa [DNSP_iff] using h3 x hx⟩

end Lemmas1

-- Give FiniteGraph a default (empty) instance
instance {α : Type} [DecidableEq α] : Inhabited (FiniteGraph α) where
  default := {
    vertices := ∅
    edges := ∅
    edge_valid := by
      intro e he
      simp at he
  }


/-! ## 2. Root-free graph notions -/

section Nbrs
variable {α : Type} [DecidableEq α] (G : FiniteGraph α)

/-- Out-neighbors of `u` that are out-neighbors of `v` (for an arc u → v). -/
def interiorNbrs (u v : α) : Finset α := if G.Adj u v then (G.N1 u ∩ G.N1 v) else ∅

/-- Second out-neighbors of `u` that are out-neighbors of `v` (for an arc u → v). -/
def exteriorNbrs (u v : α) : Finset α := if G.Adj u v then (G.N2 u ∩ G.N1 v) else ∅

/-- Arcs u→c and v→c for each interior neighbour c of the pair (u,v). No guards. -/
def interiorArcs (u v : α) : Finset (α × α) :=
  (G.interiorNbrs u v).image (fun c => (u, c)) ∪
  (G.interiorNbrs u v).image (fun c => (v, c))

/-- Walk of exactly `n` edges from `u` to `v`, extended at the end (matches BFS). -/
inductive PathLen : α → α → Nat → Prop
  | refl (u : α) : PathLen u u 0
  | tail {u v w : α} {n : Nat} : PathLen u v n → G.Adj v w → PathLen u w (n + 1)

/-- The shortest path length is the least `n` for which a path exists. -/
def ShortestPathLen (u v : α) (n : Nat) : Prop :=
  PathLen G u v n ∧ ∀ m, PathLen G u v m → n ≤ m

/-- Remove the arc x → c. Same vertices, so `edge_valid` is inherited. -/
def removeArc (x c : α) : FiniteGraph α where
  vertices := G.vertices
  edges := G.edges.erase (x, c)
  edge_valid := fun e he => G.edge_valid e (Finset.mem_of_mem_erase he)

end Nbrs

section NbrLemmas
variable {α : Type} [DecidableEq α] {G : FiniteGraph α}

lemma ShortestPathLen.unique {u v : α} {n m : Nat}
    (h₁ : G.ShortestPathLen u v n) (h₂ : G.ShortestPathLen u v m) : n = m :=
  le_antisymm (h₁.2 m h₂.1) (h₂.2 n h₁.1)

lemma mem_interiorNbrs {u v w : α} :
    w ∈ G.interiorNbrs u v ↔ G.Adj u v ∧ G.Adj u w ∧ G.Adj v w := by
  unfold interiorNbrs
  split_ifs with h <;> simp [h]

lemma mem_exteriorNbrs {u v w : α} :
    w ∈ G.exteriorNbrs u v ↔
      G.Adj u v ∧ (((∃ x, G.Adj u x ∧ G.Adj x w) ∧ w ≠ u ∧ ¬ G.Adj u w) ∧ G.Adj v w) := by
  unfold exteriorNbrs
  split_ifs with h
  · simp [h, mem_N2]
  · simp [h]

lemma interiorNbrs_subset_N1 (u v : α) : G.interiorNbrs u v ⊆ G.N1 u := by
  unfold interiorNbrs
  split_ifs
  · exact Finset.inter_subset_left
  · exact Finset.empty_subset _

lemma exteriorNbrs_subset_N2 (u v : α) : G.exteriorNbrs u v ⊆ G.N2 u := by
  unfold exteriorNbrs
  split_ifs
  · exact Finset.inter_subset_left
  · exact Finset.empty_subset _

/-- "Out-degree at least doubles in the square" is Seymour at `u`. -/
lemma doubling_iff_seymour (u : α) :
    2 * G.cardN1 u ≤ (G.N1 u ∪ G.N2 u).card ↔ G.cardN1 u ≤ G.cardN2 u := by
  rw [Finset.card_union_of_disjoint (disjoint_N1_N2 u)]
  unfold cardN1 cardN2
  omega

/-- Dual of Lemma 4: every second neighbour is reached through some `v ∈ N⁺(u)`. No premise needed. -/
lemma N2_eq_biUnion_ext (u : α) :
    G.N2 u = (G.N1 u).biUnion (fun v => G.exteriorNbrs u v) := by
  ext w
  rw [mem_N2, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨v, huv, hvw⟩, hwu, hnot⟩
    exact ⟨v, mem_N1.2 huv, mem_exteriorNbrs.2 ⟨huv, ⟨⟨v, huv, hvw⟩, hwu, hnot⟩, hvw⟩⟩
  · rintro ⟨v, -, hw⟩
    obtain ⟨-, ⟨hex, hne, hnot⟩, -⟩ := mem_exteriorNbrs.1 hw
    exact ⟨hex, hne, hnot⟩

lemma interior_exterior_disjoint (u v : α) :
    Disjoint (G.interiorNbrs u v) (G.exteriorNbrs u v) :=
  (disjoint_N1_N2 u).mono (interiorNbrs_subset_N1 u v) (exteriorNbrs_subset_N2 u v)

theorem interior_neighbors_implies_first_neighbors {u v c : α}
    (h : c ∈ G.interiorNbrs u v) : c ∈ G.N1 u ∧ c ∈ G.N1 v :=
  ⟨mem_N1.2 (mem_interiorNbrs.1 h).2.1, mem_N1.2 (mem_interiorNbrs.1 h).2.2⟩

/-- Needs the arc `u → v`: otherwise `exteriorNbrs u v = ∅`. -/
theorem mem_exteriorNbrs_iff {u v c : α} (h : G.Adj u v) :
    c ∈ G.exteriorNbrs u v ↔ c ∈ G.N2 u ∧ c ∈ G.N1 v := by
  unfold exteriorNbrs
  rw [if_pos h]
  exact Finset.mem_inter

lemma interiorArcs_adj {u v a b : α} (h : (a, b) ∈ G.interiorArcs u v) :
    G.Adj a b := by
  simp only [interiorArcs, Finset.mem_union, Finset.mem_image] at h
  rcases h with ⟨c, hc, he⟩ | ⟨c, hc, he⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact (mem_interiorNbrs.1 hc).2.1      -- Adj u c
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact (mem_interiorNbrs.1 hc).2.2      -- Adj v c

lemma N1_eq_int_union_ext (hG : G.IsOriented) {u v : α} (huv : G.Adj u v) :
    G.N1 v = G.interiorNbrs u v ∪ G.exteriorNbrs u v := by
  ext x
  rw [Finset.mem_union, mem_N1, mem_interiorNbrs, mem_exteriorNbrs]
  constructor
  · intro hvx
    by_cases hux : G.Adj u x
    · exact Or.inl ⟨huv, hux, hvx⟩
    · refine Or.inr ⟨huv, ⟨⟨v, huv, hvx⟩, ?_, hux⟩, hvx⟩
      rintro rfl
      have h := hG.2 _ _ huv hvx
      subst h
      exact hG.1 _ huv.mem_vertices.1 huv
  · rintro (⟨-, -, hvx⟩ | ⟨-, -, hvx⟩) <;> exact hvx

lemma cardN1_eq_int_add_ext (hG : G.IsOriented) {u v : α} (huv : G.Adj u v) :
    G.cardN1 v = (G.interiorNbrs u v).card + (G.exteriorNbrs u v).card := by
  unfold cardN1
  rw [N1_eq_int_union_ext hG huv,
    Finset.card_union_of_disjoint (interior_exterior_disjoint u v)]

/-- With rigidity `|I| = j`, the exterior set has at least `δ − j` elements. -/
lemma ext_card_ge {u v : α} {δ j : Nat} (hG : G.IsOriented) (huv : G.Adj u v)
    (hδ : δ ≤ G.cardN1 v) (hint : (G.interiorNbrs u v).card = j) :
    δ - j ≤ (G.exteriorNbrs u v).card := by
  have := cardN1_eq_int_add_ext hG huv
  omega

lemma adj_removeArc {x c u v : α} :
    (G.removeArc x c).Adj u v ↔ (u, v) ≠ (x, c) ∧ G.Adj u v := by
  simp [removeArc, Adj, Finset.mem_erase]

lemma N1_eq_biUnion_int {u : α}
    (h : ∀ x ∈ G.N1 u, ∃ v ∈ G.N1 u, G.Adj v x) :
    G.N1 u = (G.N1 u).biUnion (fun v => G.interiorNbrs u v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := h x hx
    exact Finset.mem_biUnion.2
      ⟨v, hv, mem_interiorNbrs.2 ⟨mem_N1.1 hv, mem_N1.1 hx, hvx⟩⟩
  · intro hx
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.1 hx
    exact mem_N1.2 (mem_interiorNbrs.1 hxv).2.1

/-- Counting form, which is how it gets used: `deg u ≤ Σ_{v ∈ N⁺(u)} |int(u,v)|`. -/
lemma cardN1_le_sum_int {u : α}
    (h : ∀ x ∈ G.N1 u, ∃ v ∈ G.N1 u, G.Adj v x) :
    G.cardN1 u ≤ ∑ v ∈ G.N1 u, (G.interiorNbrs u v).card := by
  unfold cardN1
  calc (G.N1 u).card
      = ((G.N1 u).biUnion (fun v => G.interiorNbrs u v)).card := by
        rw [← N1_eq_biUnion_int h]
    _ ≤ ∑ v ∈ G.N1 u, (G.interiorNbrs u v).card := Finset.card_biUnion_le

/-- Lemma 9 (Exterior Load Balancing). If `x` is non-Seymour, every exterior set
    `ext(x,y)` is smaller than the out-degree of `x`. -/
lemma ext_card_lt_outdeg {x : α} (hx : G.cardN2 x < G.cardN1 x) (y : α) :
    (G.exteriorNbrs x y).card < G.cardN1 x := by
  have h : (G.exteriorNbrs x y).card ≤ G.cardN2 x :=
    Finset.card_le_card (exteriorNbrs_subset_N2 x y)
  omega

end NbrLemmas

/-! ## 3. BFS from an explicit root `s` (raw machinery) -/

section Defs2
variable {α : Type} [DecidableEq α] (G : FiniteGraph α)

def bfsState (s : α) : Nat → Finset α × Finset α
  | 0 => (∅, ({s} : Finset α).filter (· ∈ G.vertices))
  | n + 1 =>
    let st := bfsState s n
    (st.1 ∪ st.2, (st.2.biUnion G.N1) \ (st.1 ∪ st.2))

def layer (s : α) (n : Nat) : Finset α := (G.bfsState s n).2
def seen  (s : α) (n : Nat) : Finset α := (G.bfsState s n).1

end Defs2

section Lemmas2
variable {α : Type} [DecidableEq α] {G : FiniteGraph α}

@[simp] lemma layer_zero (s : α) :
    G.layer s 0 = ({s} : Finset α).filter (· ∈ G.vertices) := rfl
@[simp] lemma seen_zero (s : α) : G.seen s 0 = ∅ := rfl
lemma seen_succ (s : α) (n : Nat) : G.seen s (n+1) = G.seen s n ∪ G.layer s n := rfl
lemma layer_succ (s : α) (n : Nat) :
    G.layer s (n+1) = ((G.layer s n).biUnion G.N1) \ (G.seen s n ∪ G.layer s n) := rfl

/-- Layer 0 is the root, when the root is a vertex. -/
lemma layer_zero_of_mem {s : α} (hs : s ∈ G.vertices) : G.layer s 0 = {s} := by
  rw [layer_zero]
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, hs⟩

/-- Layer 1 is the out-neighborhood of the root minus the root itself. -/
lemma layer_one_eq {s : α} (hs : s ∈ G.vertices) : G.layer s 1 = G.N1 s \ {s} := by
  show G.layer s (0 + 1) = G.N1 s \ {s}
  rw [layer_succ, layer_zero_of_mem hs, seen_zero, Finset.singleton_biUnion,
    Finset.empty_union]

lemma disjoint_layer_seen (s : α) (n : Nat) : Disjoint (G.layer s n) (G.seen s n) := by
  cases n with
  | zero => simp
  | succ n => rw [layer_succ, seen_succ]; exact Finset.sdiff_disjoint

lemma layer_subset_seen {s : α} {m n : Nat} (h : m < n) : G.layer s m ⊆ G.seen s n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [seen_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact (ih h).trans Finset.subset_union_left
    · exact Finset.subset_union_right

lemma disjoint_layers {s : α} {m n : Nat} (h : m < n) :
    Disjoint (G.layer s m) (G.layer s n) :=
  ((disjoint_layer_seen s n).mono_right (layer_subset_seen h)).symm

lemma layer_subset_vertices (s : α) (n : Nat) : G.layer s n ⊆ G.vertices := by
  cases n with
  | zero => intro v hv; exact (Finset.mem_filter.1 hv).2
  | succ n =>
    intro v hv
    rw [layer_succ] at hv
    obtain ⟨hv, -⟩ := Finset.mem_sdiff.1 hv
    obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.1 hv
    exact N1_subset_vertices hu

lemma layer_succ_eq_empty {s : α} {n : Nat} (h : G.layer s n = ∅) :
    G.layer s (n+1) = ∅ := by
  rw [layer_succ, h]; simp

lemma seen_subset_vertices (s : α) (n : Nat) : G.seen s n ⊆ G.vertices := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [seen_succ]
    exact Finset.union_subset ih (layer_subset_vertices s n)

lemma layer_nonempty_of_le {s : α} {j n : Nat} (hjn : j ≤ n)
    (h : (G.layer s n).Nonempty) : (G.layer s j).Nonempty := by
  induction n with
  | zero =>
    have hj : j = 0 := by omega
    subst hj
    exact h
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · apply ih (by omega)
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 := layer_succ_eq_empty hne
      rw [h0] at h
      simp at h
    · have hj : j = n + 1 := by omega
      subst hj
      exact h

lemma card_seen_ge {s : α} (n : Nat)
    (h : ∀ j, j < n → (G.layer s j).Nonempty) : n ≤ (G.seen s n).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : n ≤ (G.seen s n).card := ih (fun j hj => h j (by omega))
    have h2 : 0 < (G.layer s n).card := Finset.card_pos.2 (h n (by omega))
    rw [seen_succ, Finset.card_union_of_disjoint (disjoint_layer_seen s n).symm]
    omega

/-- A nonempty layer `m` forces `m < |V|`. -/
lemma layer_index_lt_card {s x : α} {m : Nat} (hx : x ∈ G.layer s m) :
    m < G.vertices.card := by
  have hne : ∀ j, j < m + 1 → (G.layer s j).Nonempty := fun j hj =>
    layer_nonempty_of_le (G := G) (s := s) (n := m) (by omega) ⟨x, hx⟩
  have h1 := card_seen_ge (G := G) (s := s) (m + 1) hne
  have h2 := Finset.card_le_card (seen_subset_vertices (G := G) s (m + 1))
  omega

end Lemmas2

/-! ## 4. Minimum out-degree vertices -/

section MinDeg
variable {α : Type} [DecidableEq α] (G : FiniteGraph α)

/-- Spec: `u` is a vertex of minimum out-degree. -/
def IsMinOutDeg (u : α) : Prop :=
  u ∈ G.vertices ∧ ∀ v ∈ G.vertices, G.cardN1 u ≤ G.cardN1 v

lemma exists_minOutDeg {G : FiniteGraph α} (h : G.vertices.Nonempty) :
    ∃ u, G.IsMinOutDeg u := by
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image G.vertices G.cardN1 h
  exact ⟨u, hu, hmin⟩

end MinDeg

section MinDegOrder
variable {α : Type} [LinearOrder α] (G : FiniteGraph α)

def minDegVertices : Finset α :=
  G.vertices.filter fun u => ∀ v ∈ G.vertices, G.cardN1 u ≤ G.cardN1 v

lemma mem_minDegVertices {G : FiniteGraph α} {u : α} :
    u ∈ G.minDegVertices ↔ G.IsMinOutDeg u := by
  unfold minDegVertices IsMinOutDeg
  exact Finset.mem_filter

end MinDegOrder

/-- The invariant, stated once. `size j` is the number of nodes in layer `j`. -/
structure ShrinkingProfile (size : Nat → Nat) (delta : Nat) : Prop where
  first : size 1 = delta
  step  : ∀ j, 1 ≤ j → size (j + 1) = size j - 1

namespace ShrinkingProfile
variable {size : Nat → Nat} {delta : Nat}

/-- Cleaner form: index `m + 1` instead of `m + 2`, so the base case is `first`. -/
theorem size_succ (h : ShrinkingProfile size delta) (m : Nat) :
    size (m + 1) = delta - m := by
  induction m with
  | zero => simpa using h.first
  | succ m ih =>
    rw [h.step (m + 1) (by omega), ih]
    omega

theorem size_add_two (h : ShrinkingProfile size delta) (m : Nat) :
    size (m + 2) = delta - (m + 1) :=
  h.size_succ (m + 1)

/-- Free consequence: layers are empty from index `delta + 1` on. -/
theorem size_eq_zero (h : ShrinkingProfile size delta) {j : Nat}
    (hj : delta < j) : size j = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [h.size_succ]; omega

end ShrinkingProfile

/-! ## 5. NEGraph: the foundation -/

/-- A graph that is nonempty by construction. -/
structure NEGraph (α : Type) [LinearOrder α] where
  G : FiniteGraph α
  nonempty : G.vertices.Nonempty

namespace NEGraph
variable {α : Type} [LinearOrder α] (N : NEGraph α)

/-! ### Root (total: no Option) -/

lemma minDeg_nonempty : N.G.minDegVertices.Nonempty := by
  obtain ⟨u, hu⟩ := exists_minOutDeg N.nonempty
  exact ⟨u, mem_minDegVertices.2 hu⟩

/-- Total: no Option. Ties go to the smallest vertex. -/
def root : α := N.G.minDegVertices.min' N.minDeg_nonempty

lemma root_spec : N.G.IsMinOutDeg N.root :=
  mem_minDegVertices.1 (Finset.min'_mem _ _)

lemma root_mem : N.root ∈ N.G.vertices := N.root_spec.1

/-- `delta` is the minimum out-degree, i.e. the out-degree of the root. -/
def delta : Nat := N.G.cardN1 N.root

lemma delta_le (v : α) (hv : v ∈ N.G.vertices) : N.delta ≤ N.G.cardN1 v :=
  N.root_spec.2 v hv

/-! ### BFS layers (total) -/

/-- BFS layer n from the root. -/
def getLayer (n : Nat) : Finset α := N.G.layer N.root n

/-- Vertices at distance < n. -/
def getSeen (n : Nat) : Finset α := N.G.seen N.root n

/-- Layers 0..card as a list: the whole BFS in one object. -/
def bfsLayers : List (Finset α) :=
  (List.range (N.G.vertices.card + 1)).map N.getLayer

lemma getLayer_zero : N.getLayer 0 = {N.root} :=
  layer_zero_of_mem N.root_mem

lemma getLayer_one : N.getLayer 1 = N.G.N1 N.root \ {N.root} :=
  layer_one_eq N.root_mem

lemma getLayer_disjoint_seen (n : Nat) : Disjoint (N.getLayer n) (N.getSeen n) :=
  disjoint_layer_seen (G := N.G) N.root n

lemma disjoint_getLayers {m n : Nat} (h : m < n) :
    Disjoint (N.getLayer m) (N.getLayer n) :=
  disjoint_layers (G := N.G) (s := N.root) h

lemma getLayer_subset_vertices (n : Nat) : N.getLayer n ⊆ N.G.vertices :=
  layer_subset_vertices (G := N.G) N.root n

lemma getSeen_succ (n : Nat) : N.getSeen (n + 1) = N.getSeen n ∪ N.getLayer n := rfl

lemma N1_subset_seen_succ_succ {u : α} {n : Nat} (hu : u ∈ N.getLayer n) :
    N.G.N1 u ⊆ N.getSeen (n + 2) := by
  intro x hx
  have hb : x ∈ (N.getLayer n).biUnion N.G.N1 := Finset.mem_biUnion.2 ⟨u, hu, hx⟩
  rw [N.getSeen_succ, N.getSeen_succ]
  by_cases h : x ∈ N.getSeen n ∪ N.getLayer n
  · exact Finset.mem_union_left _ h
  · apply Finset.mem_union_right
    exact Finset.mem_sdiff.2 ⟨hb, h⟩

/-! ### Distances.  `distOpt` is the honest Option; `dist` is total, and sends
    unreachable vertices to the sentinel `card + 1`. -/

def distOpt (v : α) : Option Nat :=
  (List.range (N.G.vertices.card + 1)).find? fun n => decide (v ∈ N.getLayer n)

/-- Total distance from the root.  Unreachable vertices get `card + 1`. -/
def dist (v : α) : Nat := (N.distOpt v).getD (N.G.vertices.card + 1)

lemma distOpt_spec {v : α} {n : Nat} (h : N.distOpt v = some n) : v ∈ N.getLayer n := by
  unfold distOpt at h
  have h' := List.find?_some h
  exact of_decide_eq_true h'

lemma dist_eq_of_distOpt {v : α} {n : Nat} (h : N.distOpt v = some n) : N.dist v = n := by
  simp [dist, h]

lemma getLayer_index_lt_card {x : α} {m : Nat} (hx : x ∈ N.getLayer m) :
    m < N.G.vertices.card :=
  layer_index_lt_card (G := N.G) (s := N.root) hx

lemma dist_of_mem_getLayer {x : α} {m : Nat} (hx : x ∈ N.getLayer m) :
    N.dist x = m := by
  have hm : m < N.G.vertices.card + 1 := by
    have := N.getLayer_index_lt_card hx
    omega
  obtain ⟨n, hn⟩ : ∃ n, N.distOpt x = some n := by
    cases h : N.distOpt x with
    | some n => exact ⟨n, rfl⟩
    | none =>
      exfalso
      unfold distOpt at h
      have h' := List.find?_eq_none.1 h m (List.mem_range.2 hm)
      simp at h'
      exact h' hx
  have hxn : x ∈ N.getLayer n := N.distOpt_spec hn
  have hnm : n = m := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Finset.disjoint_left.1 (N.disjoint_getLayers hlt) hxn hx
    · exact Finset.disjoint_left.1 (N.disjoint_getLayers hgt) hx hxn
  rw [N.dist_eq_of_distOpt hn]
  exact hnm

/-- A reached vertex lies in the layer given by its (total) distance. -/
lemma mem_getLayer_dist {v : α} {n : Nat} (h : N.distOpt v = some n) :
    v ∈ N.getLayer (N.dist v) := by
  rw [N.dist_eq_of_distOpt h]
  exact N.distOpt_spec h

/-- Rank of `v` inside its own layer (total). -/
def lexId (v : α) : Nat := ((N.getLayer (N.dist v)).sort (· ≤ ·)).idxOf v

/-- (dist, lexId) in one go (total). -/
def coord (v : α) : Nat × Nat := (N.dist v, N.lexId v)

/-! ### Components -/

/-- Everything BFS reaches: the root's component. -/
def reached : Finset α := N.G.vertices.filter fun v => (N.distOpt v).isSome

/-- Everything else: the other components. -/
def unreached : Finset α := N.G.vertices.filter fun v => (N.distOpt v).isNone

/-! ### Neighbor sets -/

/-- Common out-neighbors of an arc u → v. -/
def getIntNbrs (u v : α) : Finset α := N.G.interiorNbrs u v

/-- Second out-neighbors of u that v points to, for an arc u → v. -/
def getExtNbrs (u v : α) : Finset α := N.G.exteriorNbrs u v

/-- Out-neighbors of v in a strictly earlier layer.
    (For an unreached `v`, `dist v = card + 1`, so this is its out-neighbors in the
    root's component.) -/
def getBackNbrs (v : α) : Finset α := N.G.N1 v ∩ N.getSeen (N.dist v)

/-- Back out-neighbors of v in the immediately previous layer (dist - 1). -/
def getConnBacks (v : α) : Finset α :=
  match N.dist v with
  | 0     => ∅
  | n + 1 => N.G.N1 v ∩ N.getLayer n

/-- Back out-neighbors of v in a layer before dist - 1 (layers 0..dist-2). -/
def getDiscBacks (v : α) : Finset α :=
  match N.dist v with
  | 0     => ∅
  | n + 1 => N.G.N1 v ∩ N.getSeen n

/-- The two pieces partition the back neighbors. -/
lemma backNbrs_eq_conn_union_disc (v : α) :
    N.getBackNbrs v = N.getConnBacks v ∪ N.getDiscBacks v := by
  unfold getBackNbrs getConnBacks getDiscBacks
  cases h : N.dist v with
  | zero =>
    show N.G.N1 v ∩ N.getSeen 0 = ∅ ∪ ∅
    simp [getSeen]
  | succ n =>
    show N.G.N1 v ∩ N.getSeen (n + 1) = N.G.N1 v ∩ N.getLayer n ∪ N.G.N1 v ∩ N.getSeen n
    rw [N.getSeen_succ, Finset.inter_union_distrib_left, Finset.union_comm]

lemma disjoint_conn_disc (v : α) :
    Disjoint (N.getConnBacks v) (N.getDiscBacks v) := by
  unfold getConnBacks getDiscBacks
  cases h : N.dist v with
  | zero =>
    show Disjoint (∅ : Finset α) ∅
    simp
  | succ n =>
    show Disjoint (N.G.N1 v ∩ N.getLayer n) (N.G.N1 v ∩ N.getSeen n)
    exact (N.getLayer_disjoint_seen n).mono
      Finset.inter_subset_right Finset.inter_subset_right

/-- No back arcs of either kind, anywhere. -/
def NoBackArcs : Prop :=
  ∀ v, N.getConnBacks v = ∅ ∧ N.getDiscBacks v = ∅

/-! ### Forward pairs and interior arcs (all rooted at `N.root`, so no root argument) -/

/-- Forward pair: arc u → v going from layer n to layer n+1. -/
def IsForwardPair (u v : α) : Prop :=
  N.G.Adj u v ∧ N.dist v = N.dist u + 1

instance (u v : α) : Decidable (N.IsForwardPair u v) := by
  unfold IsForwardPair; infer_instance

/-- All interior arcs, over every forward pair. -/
def allInteriorArcs : Finset (α × α) :=
  ((N.G.vertices ×ˢ N.G.vertices).filter fun p => N.IsForwardPair p.1 p.2).biUnion
    fun p => N.G.interiorArcs p.1 p.2

def interiorOutDegree (x : α) : Nat :=
  (N.allInteriorArcs.filter (fun a => a.1 = x)).card

def interiorInDegree (x : α) : Nat :=
  (N.allInteriorArcs.filter (fun a => a.2 = x)).card

def totalInteriorDegree (x : α) : Nat :=
  N.interiorInDegree x + N.interiorOutDegree x

def maxTotalInteriorDegree : Nat :=
  N.G.vertices.sup fun w => N.totalInteriorDegree w

def interiorArcCount : Nat := N.allInteriorArcs.card

/-! ### Order on vertices -/

/-- (distance from root, vertex). Unreachable vertices sort after every layer. -/
def rootKey (v : α) : Nat ×ₗ α := toLex (N.dist v, v)

/-- BFS-Lex order: by layer, then by position within the layer. -/
def Lt (a b : α) : Prop := N.rootKey a < N.rootKey b

lemma rootKey_injective : Function.Injective N.rootKey := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  simpa [rootKey] using this

/-- Well-founded whenever `<` on `α` is (true for `Nat`). -/
theorem Lt_wf [WellFoundedLT α] : WellFounded N.Lt :=
  InvImage.wf N.rootKey wellFounded_lt

/-! ### Counterexamples and the minimum counterexample -/

def IsCounterexample : Prop := N.G.IsCounterexample

lemma DNSP_of_counterexample (hC : N.IsCounterexample) {x : α}
    (hx : x ∈ N.G.vertices) : N.G.DNSP x :=
  FiniteGraph.DNSP_iff.2 (hC.2.2 x hx)

lemma root_irrefl (hC : N.IsCounterexample) : ¬ N.G.Adj N.root N.root :=
  hC.1.1 N.root N.root_mem

/-- Lexicographic metric: interior-arc count first, then max interior degree.
    Total, because the root is. -/
def mceMetric : Lex (Nat × Nat) :=
  toLex (N.interiorArcCount, N.maxTotalInteriorDegree)

def IsMinimumCounterexample : Prop :=
  N.IsCounterexample ∧
  ∀ M : NEGraph α, M.IsCounterexample → N.mceMetric ≤ M.mceMetric

/-- If a counterexample exists, a minimum one exists. -/
theorem exists_minimumCounterexample (hN : N.IsCounterexample) :
    ∃ M : NEGraph α, M.IsMinimumCounterexample := by
  obtain ⟨M, hM, hmin⟩ :=
    (InvImage.wf (NEGraph.mceMetric (α := α)) wellFounded_lt).has_min
      {M : NEGraph α | M.IsCounterexample} ⟨N, hN⟩
  exact ⟨M, hM, fun H hH => not_lt.1 (hmin H hH)⟩

/-- Remove the arc x → c.  Stays an `NEGraph` (same vertices); the root is simply
    recomputed, so there is no Option to thread through. -/
def removeArc (x c : α) : NEGraph α where
  G := N.G.removeArc x c
  nonempty := N.nonempty

theorem mce_not_reducible {H M : NEGraph α}
    (hmce : H.IsMinimumCounterexample) (hM : M.IsCounterexample) :
    ¬ M.mceMetric < H.mceMetric :=
  not_lt.2 (hmce.2 M hM)

theorem mceMetric_lt_of_arcs_lt {M H : NEGraph α}
    (h : M.interiorArcCount < H.interiorArcCount) : M.mceMetric < H.mceMetric := by
  unfold mceMetric
  rw [Prod.Lex.lt_iff]
  exact Or.inl h

theorem not_mce_of_removable (x c : α)
    (hlt  : (N.removeArc x c).interiorArcCount < N.interiorArcCount)
    (hcex : (N.removeArc x c).IsCounterexample) :
    ¬ N.IsMinimumCounterexample := by
  intro hmce
  exact mce_not_reducible hmce hcex (mceMetric_lt_of_arcs_lt hlt)

/-! ### Layer sizes -/

def size (n : Nat) : Nat := (N.getLayer n).card

/-- Replaces h_v0_deg, h_v0_nodup, h_layer1_eq. Uses only irreflexivity,
    which comes from `IsOriented`. -/
lemma size_one (hirr : ¬ N.G.Adj N.root N.root) : N.size 1 = N.delta := by
  show (N.G.layer N.root 1).card = (N.G.N1 N.root).card
  rw [layer_one_eq N.root_mem, Finset.sdiff_singleton_eq_erase,
    Finset.erase_eq_of_notMem (fun h => hirr (mem_N1.1 h))]

/-- The one structural claim. Your old `h_step`. -/
def Shrinks : Prop := ∀ j, 1 ≤ j → N.size (j + 1) = N.size j - 1

lemma size_succ_formula (hirr : ¬ N.G.Adj N.root N.root) (hs : N.Shrinks) (m : Nat) :
    N.size (m + 1) = N.delta - m := by
  induction m with
  | zero => simpa using N.size_one hirr
  | succ m ih => rw [hs (m + 1) (by omega), ih]; omega

/-- Your old statement. -/
theorem layer_size_formula (hirr : ¬ N.G.Adj N.root N.root) (hs : N.Shrinks) (m : Nat) :
    N.size (m + 2) = N.delta - (m + 1) :=
  N.size_succ_formula hirr hs (m + 1)

/-- `|R_i| = δ - i + 1` for `1 ≤ i ≤ δ`. -/
theorem size_formula_of_shrinks (hirr : ¬ N.G.Adj N.root N.root) (hs : N.Shrinks) :
    ∀ i, 1 ≤ i → i ≤ N.delta → N.size i = N.delta - i + 1 := by
  intro i hi hid
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [N.size_succ_formula hirr hs m]
  omega

def ShrinksLE : Prop := ∀ j, 1 ≤ j → N.size (j + 1) ≤ N.size j - 1   -- pigeonhole, non-Seymour
def ShrinksGE : Prop := ∀ j, 1 ≤ j → N.size j - 1 ≤ N.size (j + 1)   -- needs a separate argument

/-! ### Main (still open) theorems -/

/-- Port of `seymour_of_disconnected_back_arc`. -/
theorem seymour_of_disc_back_arc {a b : α} (hab : N.G.Adj a b) (hba : ¬ N.G.Adj b a)
    (hdisj : ∀ z, z ∈ N.G.N1 b → z ∉ N.G.N1 a)
    (hreg : N.G.cardN1 a ≤ N.delta) :
    N.G.cardN1 a ≤ N.G.cardN2 a := by
  have hsub : N.G.N1 b ⊆ N.G.N2 a := by
    intro z hz
    have hbz : N.G.Adj b z := mem_N1.1 hz
    refine mem_N2.2 ⟨⟨b, hab, hbz⟩, ?_, ?_⟩
    · rintro rfl
      exact hba hbz
    · exact fun h => hdisj z hz (mem_N1.2 h)
  have hb : b ∈ N.G.vertices := hab.mem_vertices.2
  have h1 : N.G.cardN1 b ≤ N.G.cardN2 a := Finset.card_le_card hsub
  have h2 := N.delta_le b hb
  omega

/-- In a counterexample, Lemma 9 holds at every vertex. -/
lemma ext_card_lt_outdeg (hC : N.IsCounterexample) {x : α}
    (hx : x ∈ N.G.vertices) (y : α) :
    (N.G.exteriorNbrs x y).card < N.G.cardN1 x :=
  FiniteGraph.ext_card_lt_outdeg
    (by simpa [FiniteGraph.isNonSeymour] using hC.2.2 x hx) y

/-- Port of `no_disconnected_back_arc`. -/
theorem no_disconnected_back_arc (hC : N.IsCounterexample) {a b : α}
    (hab : N.G.Adj a b)
    (hreg : N.G.cardN1 a ≤ N.delta)
    (hpath : (∃ z, z ∈ N.G.N1 b ∧ z ∈ N.G.N1 a) →
        ∃ x ∈ N.G.vertices, N.G.cardN1 x ≤ N.G.cardN2 x) :
    False := by
  have hall : ∀ x ∈ N.G.vertices, ¬ (N.G.cardN1 x ≤ N.G.cardN2 x) := by
    intro x hx hle
    have h := hC.2.2 x hx
    simp [isNonSeymour] at h
    omega
  have hba : ¬ N.G.Adj b a := by
    intro hba
    have h := hC.1.2 a b hab hba
    subst h
    exact hC.1.1 _ hab.mem_vertices.1 hab
  by_cases hint : ∃ z, z ∈ N.G.N1 b ∧ z ∈ N.G.N1 a
  · obtain ⟨x, hx, hle⟩ := hpath hint
    exact hall x hx hle
  · push_neg at hint
    exact hall a hab.mem_vertices.1 (N.seymour_of_disc_back_arc hab hba hint hreg)
end NEGraph

/- Part 2a: in a counterexample, no connected back arcs.-/
-- theorem no_conn_backs (hC : N.IsCounterexample) (v : α) :
--     N.getConnBacks v = ∅ := by
--   sorry

-- /-- Glue: the hypothesis `NoBackArcs` is discharged here. -/
-- theorem noBackArcs_of_counterexample (hC : N.IsCounterexample) : N.NoBackArcs :=
--  fun v => ⟨N.no_conn_backs hC v, N.no_disconnected_back_arcs hC v⟩

-- /-- THE theorem. Proved by: no back arcs (Part 2), then the structure (Part 1). -/
-- theorem shrinks_of_counterexample (hC : N.IsCounterexample) : N.Shrinks := by
--  sorry

-- /-- Fully discharged: the only premise is that N is a counterexample. -/
-- theorem layer_size_formula_of_counterexample (hC : N.IsCounterexample) (m : Nat) :
--     N.size (m + 2) = N.delta - (m + 1) :=
--  N.layer_size_formula (N.root_irrefl hC) (N.shrinks_of_counterexample hC) m

-- uses: shrinks_of_counterexample, interiorDeg_eq (k per vertex in layer k),
--       arcs_within_le_choose, no_layer
-- theorem false_of_counterexample (hC : N.IsCounterexample) : False := by
--  sorry


/-! ## 6. Sanity checks -/

def profile (δ : Nat) : List Nat :=
  1 :: (List.range (δ + 1)).map fun m => δ - m   -- sizes of layers 0,1,2,...

#eval profile 7                -- [1, 7, 6, 5, 4, 3, 2, 1, 0]
#eval (profile 7).sum

def G7 : FiniteGraph Nat :=
  { vertices := Finset.range 8
    edges := (List.range 7).foldl (fun s i => insert (0, i+1) s) (∅ : Finset (Nat × Nat))
             ∪ (List.range 7).foldl (fun s i => insert (i+1, (i+1) % 7 + 1) s)
                 (∅ : Finset (Nat × Nat))
    edge_valid := by decide }

#eval (List.range 4).map fun n => (G7.layer 0 n).card   -- [1, 7, 0, 0]
#eval (G7.cardN1 1, G7.cardN2 1)

def layerSize (δ k : Nat) : Nat := δ + 1 - k

def firstBad (δ : Nat) : Option Nat :=
  (List.range' 1 δ).find? fun k =>
    decide (Nat.choose (layerSize δ k) 2 < k * layerSize δ k)

def nodesThrough (δ k : Nat) : Nat :=
  1 + ((List.range' 1 k).map (layerSize δ)).sum

#eval firstBad 7                                   -- some 3
#eval (firstBad 7).map (nodesThrough 7)            -- some 19
#eval (List.range' 1 12).map fun δ => (δ, firstBad δ)

/-! ## 7. Pure arithmetic / generic lemmas (no graph structure needed) -/

/-- (The original statement was false for `m = 0`, so `0 < m` was added.) -/
lemma no_layer (k m : Nat) (hm : 0 < m)
    (h : k * m ≤ Nat.choose m 2) : 2 * k + 1 ≤ m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Nat.choose_two_right] at h
  have h2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 h
  have e : t + 1 - 1 = t := by omega
  rw [e] at h2
  have h3 : (t + 1) * (2 * k) ≤ (t + 1) * t := by
    calc (t + 1) * (2 * k) = k * (t + 1) * 2 := by ring
      _ ≤ (t + 1) * t := h2
  have h4 : 2 * k ≤ t := Nat.le_of_mul_le_mul_left h3 (by omega)
  omega

theorem maxInDeg_eq_one_iff_bijective {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) :
    (∀ y, (Finset.univ.filter (fun x => f x = y)).card ≤ 1) ↔ Function.Bijective f := by
  rw [← Finite.injective_iff_bijective]
  constructor
  · intro h x x' hxx'
    by_contra hne
    have h2 : 1 < (Finset.univ.filter (fun z => f z = f x)).card := by
      rw [Finset.one_lt_card]
      exact ⟨x, by simp, x', by simp [hxx'.symm], hne⟩
    have := h (f x)
    omega
  · intro hinj y
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp at ha hb
    exact hinj (ha.trans hb.symm)

theorem layer_bound_of_step (s : Nat → Nat) (δ : Nat)
    (h1 : s 1 = δ) (hstep : ∀ j, 1 ≤ j → s (j + 1) ≤ s j - 1) :
    ∀ m, s (m + 2) ≤ δ - (m + 1) := by
  intro m
  induction m with
  | zero =>
    have h : s 2 ≤ s 1 - 1 := hstep 1 le_rfl
    show s 2 ≤ δ - (0 + 1)
    omega
  | succ m ih =>
    have h : s (m + 3) ≤ s (m + 2) - 1 := hstep (m + 2) (by omega)
    show s (m + 3) ≤ δ - (m + 1 + 1)
    omega

theorem interior_lower_bound (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hback : backC = 0)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    k + 1 ≤ intC := by omega

/-- Back arcs forced by interior deficiency (no load balance, no minimality). -/
theorem back_ge_deficiency (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    (k + 1) - intC ≤ backC := by omega

theorem too_few_interior_old (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ)
    (hdef : intC < k + 1) : 0 < backC := by omega

theorem interior_ge_of_layers {β : Type*} [DecidableEq β]
    (out A B : Finset β) (delta k : Nat)
    (hdeg : delta ≤ out.card)
    (hsub : out ⊆ A ∪ B)            -- BFS + no back arcs: A = R_k, B = R_{k+1}
    (hB : B.card ≤ delta - k)       -- from the layer formula
    (hk : k ≤ delta) :
    k ≤ (out ∩ A).card := by
  have h1 : out ⊆ (out ∩ A) ∪ B := by
    intro x hx
    rcases Finset.mem_union.mp (hsub hx) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, h⟩)
    · exact Finset.mem_union_right _ h
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  omega

theorem chain_ends_measure {α : Type*} (μ : α → Nat) (P Closes : α → Prop)
    (h0 : ∃ a, P a)
    (hstep : ∀ a, P a → Closes a ∨ ∃ b, P b ∧ μ b < μ a) :
    ∃ a, P a ∧ Closes a := by
  obtain ⟨a, ha, hmin⟩ :=
    (InvImage.wf μ wellFounded_lt).has_min {a | P a} h0
  rcases hstep a ha with hc | ⟨b, hb, hlt⟩
  · exact ⟨a, ha, hc⟩
  · exact absurd hlt (hmin b hb)



theorem int_not_too_low
    (δ k int_d fwd_d back_d : Nat)
    (h_deg   : δ ≤ int_d + fwd_d + back_d)   -- out-degree ≥ δ
    (h_noback : back_d = 0)
    (h_case1 : fwd_d + k ≤ δ)                -- case 1: no extra forward arcs
    : ¬ int_d < k := by
  intro h_low
  omega

theorem interior_degree_rigidity_old
  (k : Nat) (int_count : Nat)
  (h_not_too_low : int_count < k → False)
  (h_not_too_high : k < int_count → False)
  : int_count = k := by
  rcases lt_trichotomy int_count k with h_lt | h_eq | h_gt
  · exact absurd h_lt (fun h => h_not_too_low h)
  · exact h_eq
  · exact absurd h_gt (fun h => h_not_too_high h)

theorem node_interior_degree_eq_k_old
  (k : Nat) (int_deg : Nat)
  (h_lower_bound : k ≤ int_deg)
  (h_upper_bound : int_deg ≤ k)
  : int_deg = k := by
  omega

theorem oriented_arcs_le {α : Type*} [DecidableEq α] (R : Finset α)
    (A : Finset (α × α)) (hA : A ⊆ R.offDiag)
    (hanti : ∀ p ∈ A, (p.2, p.1) ∉ A) :
    2 * A.card ≤ R.card * R.card - R.card := by
  have hsw : (A.image Prod.swap) ⊆ R.offDiag := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := Finset.mem_offDiag.mp (hA hq)
    exact Finset.mem_offDiag.mpr ⟨this.2.1, this.1, fun h => this.2.2 h.symm⟩
  have hdis : Disjoint A (A.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hpA hpI
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hpI
    exact hanti q hq hpA
  have hcard : (A.image Prod.swap).card = A.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have := Finset.card_le_card (Finset.union_subset hA hsw)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.offDiag_card] at this
  omega

theorem no_layer_past_third (δ : Nat) (hδ : 1 ≤ δ)
    (hlayer : ∀ i, 1 ≤ i → i ≤ δ → 3 * i ≤ δ) : False := by
  have := hlayer (δ / 3 + 1) (by omega) (by omega)
  omega

theorem last_layer_le (δ i : Nat) (h : 3 * i ≤ δ) : i ≤ δ / 3 := by omega

theorem first_forbidden (δ : Nat) : ¬ (3 * (δ / 3 + 1) ≤ δ) := by omega

theorem feasibility (n i δ : Nat) (hn : n = δ - i + 1) (hi : i ≤ δ)
    (h : 2 * (n * i) ≤ n * n - n) : 3 * i ≤ δ := by
  have hpos : 0 < n := by omega
  have h2 : n * (2 * i) ≤ n * (n - 1) := by
    have e1 : n * (2 * i) = 2 * (n * i) := Nat.mul_left_comm n 2 i
    have e2 : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
    rw [e1, e2]
    exact h
  have h3 : 2 * i ≤ n - 1 := Nat.le_of_mul_le_mul_left h2 hpos
  omega

/-- Layers collapse at depth ⌊δ/3⌋: the size formula and the interior-arc
    capacity bound cannot both hold at layer ⌊δ/3⌋ + 1. -/
theorem layers_collapse (δ : Nat) (hδ : 1 ≤ δ) (s : Nat → Nat)
    (hsize : ∀ i, 1 ≤ i → i ≤ δ → s i = δ - i + 1)
    (hcap  : ∀ i, 1 ≤ i → i ≤ δ → 2 * (s i * i) ≤ s i * s i - s i) :
    False := by
  have hi1 : 1 ≤ δ / 3 + 1 := by omega
  have hi2 : δ / 3 + 1 ≤ δ := by omega
  have h3 := feasibility (s (δ / 3 + 1)) (δ / 3 + 1) δ
    (hsize _ hi1 hi2) hi2 (hcap _ hi1 hi2)
  omega


namespace NEGraph
variable {α : Type} [LinearOrder α] (N : NEGraph α)

/-- Ported from `layers_collapse_G`, now for `NEGraph`. -/
theorem layers_collapse_N (hδ : 1 ≤ N.delta)
    (hsize : ∀ i, 1 ≤ i → i ≤ N.delta → N.size i = N.delta - i + 1)
    (hcap : ∀ i, 1 ≤ i → i ≤ N.delta →
      2 * (N.size i * i) ≤ N.size i * N.size i - N.size i) :
    False :=
  layers_collapse N.delta hδ N.size hsize hcap

lemma N1_subset_layer_union {v : α} {n : Nat} (hv : v ∈ N.getLayer n)
    (hback : N.G.N1 v ∩ N.getSeen n = ∅) :
    N.G.N1 v ⊆ N.getLayer n ∪ N.getLayer (n + 1) := by
  intro x hx
  have h : x ∈ (N.getSeen n ∪ N.getLayer n) ∪ N.getLayer (n + 1) :=
    N.N1_subset_seen_succ_succ hv hx
  rcases Finset.mem_union.1 h with h | h
  · rcases Finset.mem_union.1 h with h | h
    · have hx' : x ∈ N.G.N1 v ∩ N.getSeen n := Finset.mem_inter.2 ⟨hx, h⟩
      rw [hback] at hx'
      simp at hx'
    · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

/-- Without further input, exterior neighbours lie in the same layer as `v` or the next one. -/
lemma ext_subset_layers {u v : α} {n : Nat} (hv : v ∈ N.getLayer n)
    (hback : N.G.N1 v ∩ N.getSeen n = ∅) :
    N.getExtNbrs u v ⊆ N.getLayer n ∪ N.getLayer (n + 1) := by
  intro c hc
  have hvc : N.G.Adj v c := (mem_exteriorNbrs.1 hc).2.2
  exact N.N1_subset_layer_union hv hback (mem_N1.2 hvc)

/-- The exact extra hypothesis needed for `ext_subset`:
    every same-layer out-neighbour of `v` is already an out-neighbour of `u`. -/
lemma ext_subset_next_layer {u v : α} {n : Nat} (hv : v ∈ N.getLayer n)
    (hback : N.G.N1 v ∩ N.getSeen n = ∅)
    (hsame : ∀ c ∈ N.getLayer n, c ∈ N.G.N1 v → c ∈ N.G.N1 u) :
    N.getExtNbrs u v ⊆ N.getLayer (n + 1) := by
  intro c hc
  rcases Finset.mem_union.1 (N.ext_subset_layers hv hback hc) with h | h
  · exfalso
    have hx := mem_exteriorNbrs.1 hc
    exact hx.2.1.2.2 (mem_N1.1 (hsame c h (mem_N1.2 hx.2.2)))
  · exact h

/-- Out-neighbours of `v` that lie in `R_{n+2}` are exterior neighbours of every parent `u ∈ R_n`. -/
lemma N1_inter_layer_subset_ext {u v : α} {n : Nat}
    (hu : u ∈ N.getLayer n) (huv : N.G.Adj u v) :
    N.G.N1 v ∩ N.getLayer (n + 2) ⊆ N.getExtNbrs u v := by
  intro c hc
  obtain ⟨hcv, hcL⟩ := Finset.mem_inter.1 hc
  have hvc : N.G.Adj v c := mem_N1.1 hcv
  have hnot : ¬ N.G.Adj u c := by
    intro h
    have hs : c ∈ N.getSeen (n + 2) := N.N1_subset_seen_succ_succ hu (mem_N1.2 h)
    exact Finset.disjoint_left.1 (N.getLayer_disjoint_seen (n + 2)) hcL hs
  have hne : c ≠ u := by
    rintro rfl
    exact Finset.disjoint_left.1 (N.disjoint_getLayers (show n < n + 2 by omega)) hu hcL
  exact mem_exteriorNbrs.2 ⟨huv, ⟨⟨v, huv, hvc⟩, hne, hnot⟩, hvc⟩

/-- The count your argument uses. -/
lemma card_N1_inter_le_ext {u v : α} {n : Nat}
    (hu : u ∈ N.getLayer n) (huv : N.G.Adj u v) :
    (N.G.N1 v ∩ N.getLayer (n + 2)).card ≤ (N.getExtNbrs u v).card :=
  Finset.card_le_card (N.N1_inter_layer_subset_ext hu huv)

/-- Companion to `mceMetric_lt_of_arcs_lt`: for step 2, equal arc count and smaller max degree. -/
theorem mceMetric_lt_of_deg_lt {M H : NEGraph α}
    (harcs : M.interiorArcCount = H.interiorArcCount)
    (hdeg : M.maxTotalInteriorDegree < H.maxTotalInteriorDegree) :
    M.mceMetric < H.mceMetric := by
  unfold mceMetric
  rw [Prod.Lex.lt_iff]
  exact Or.inr ⟨harcs, hdeg⟩

/-- Arc-level `interior_lb_node`. `dist v` plays the role of `k + 1`. -/
theorem interior_lb_node (hC : N.IsCounterexample) {u v : α}
    (hfwd : N.IsForwardPair u v) (hv : v ∈ N.G.vertices)
    (hext : (N.getExtNbrs u v).card ≤ N.delta - N.dist v)
    (hj : N.dist v ≤ N.delta) :
    N.dist v ≤ (N.getIntNbrs u v).card := by
  have hdeg : N.delta ≤ N.G.cardN1 v := N.delta_le v hv
  have hpart : N.G.cardN1 v = (N.getIntNbrs u v).card + (N.getExtNbrs u v).card :=
    cardN1_eq_int_add_ext hC.1 hfwd.1
  omega

/-- What non-Seymour gives directly: the exterior set of an arc is smaller than the parent's out-degree. -/
lemma ext_card_lt_cardN1 (hC : N.IsCounterexample) {u v : α}
    (hu : u ∈ N.G.vertices) :
    (N.getExtNbrs u v).card < N.G.cardN1 u := by
  have h : N.G.cardN2 u < N.G.cardN1 u := by
    simpa [FiniteGraph.isNonSeymour] using hC.2.2 u hu
  have h2 : (N.getExtNbrs u v).card ≤ N.G.cardN2 u :=
    Finset.card_le_card (N.G.exteriorNbrs_subset_N2 u v)
  omega

lemma getLayer_two_subset_N2 : N.getLayer 2 ⊆ N.G.N2 N.root := by
  intro w hw
  have hw' : w ∈ N.G.layer N.root (1 + 1) := hw
  rw [layer_succ] at hw'
  obtain ⟨hb, hn⟩ := Finset.mem_sdiff.1 hw'
  obtain ⟨v, hv, hwv⟩ := Finset.mem_biUnion.1 hb
  have hv' : v ∈ N.getLayer 1 := hv
  rw [N.getLayer_one] at hv'
  obtain ⟨hvN1, -⟩ := Finset.mem_sdiff.1 hv'
  have hs1 : N.G.seen N.root 1 = {N.root} := by
    show N.G.seen N.root (0 + 1) = _
    rw [seen_succ, seen_zero, layer_zero_of_mem N.root_mem, Finset.empty_union]
  have hl1 : N.G.layer N.root 1 = N.G.N1 N.root \ {N.root} :=
    layer_one_eq N.root_mem
  rw [hs1, hl1] at hn
  have hne : w ≠ N.root := by
    intro h
    apply hn
    rw [h]
    simp
  have hnot : ¬ N.G.Adj N.root w := by
    intro h
    apply hn
    exact Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.2
      ⟨mem_N1.2 h, by simpa using hne⟩))
  exact mem_N2.2 ⟨⟨v, mem_N1.1 hvN1, mem_N1.1 hwv⟩, hne, hnot⟩

theorem size_le_of_step (s : Nat → Nat) (δ : Nat) (h1 : s 1 ≤ δ)
    (hstep : ∀ j, 1 ≤ j → s (j + 1) ≤ s j - 1) :
    ∀ m, s (m + 1) ≤ δ - m := by
  intro m
  induction m with
  | zero => simpa using h1
  | succ m ih =>
    have := hstep (m + 1) (by omega)
    omega

lemma size_zero : N.size 0 = 1 := by
  show (N.getLayer 0).card = 1
  rw [N.getLayer_zero]
  simp

/-- Base case `|C₁| ≤ δ`; it needs no irreflexivity. -/
lemma size_one_le_delta : N.size 1 ≤ N.delta := by
  show (N.G.layer N.root 1).card ≤ (N.G.N1 N.root).card
  rw [layer_one_eq N.root_mem]
  exact Finset.card_le_card Finset.sdiff_subset

/-- Lemma 11 for `NEGraph`. -/
theorem size_le_delta_sub (hle : N.ShrinksLE) (m : Nat) :
    N.size (m + 1) ≤ N.delta - m :=
  size_le_of_step N.size N.delta N.size_one_le_delta hle m

/-- This is exactly the `hext` that `interior_lb_node` needs. -/
lemma ext_card_le_of_le (hle : N.ShrinksLE) {u v : α}
    (hsub : N.getExtNbrs u v ⊆ N.getLayer (N.dist v + 1)) :
    (N.getExtNbrs u v).card ≤ N.delta - N.dist v :=
  (Finset.card_le_card hsub).trans (N.size_le_delta_sub hle (N.dist v))

/-- The file's `ShrinksLE` is Lemma 10, once the emptiness cases are set aside. -/
lemma lemma10_of_shrinksLE (hle : N.ShrinksLE) {i : Nat} (hi : 1 ≤ i)
    (h1 : 0 < N.size i) (h2 : 0 < N.size (i + 1)) :
    N.size (i + 1) < N.size i := by
  have := hle i hi
  omega

/-- Lemma 10 gives `≤`, `ext_card_ge` gives `≥`; together they give `Shrinks`. -/
lemma shrinks_of_le_ge (hle : N.ShrinksLE) (hge : N.ShrinksGE) : N.Shrinks :=
  fun j hj => le_antisymm (hle j hj) (hge j hj)

/-- The case where non-Seymour alone is enough: children of the root. -/
theorem interior_lb_root_child (hC : N.IsCounterexample) {v : α}
    (hfwd : N.IsForwardPair N.root v) (hv : v ∈ N.G.vertices)
    (hd : N.dist v = 1) :
    1 ≤ (N.getIntNbrs N.root v).card := by
  have hlt := N.ext_card_lt_cardN1 (v := v) hC N.root_mem
  have hroot : N.G.cardN1 N.root = N.delta := rfl
  have hpos : 0 < N.delta :=
    Finset.card_pos.2 ⟨v, mem_N1.2 hfwd.1⟩
  have := N.interior_lb_node hC hfwd hv (by rw [hd]; omega) (by omega)
  omega

/-- Every vertex has at least `δ` out-neighbours (card form). -/
lemma delta_le_card (v : α) (hv : v ∈ N.G.vertices) :
    N.delta ≤ (N.G.N1 v).card := N.delta_le v hv

/-- No membership hypothesis needed for the head of an arc. -/
lemma delta_le_of_adj {u v : α} (h : N.G.Adj u v) : N.delta ≤ N.G.cardN1 v :=
  N.delta_le v h.mem_vertices.2

/-- Port of `layer_succ_subset_out`: a tight exterior set forces `x` to point to the whole next layer. -/
theorem layer_succ_subset_N1 (u x : α)
    (hsub : N.getExtNbrs u x ⊆ N.getLayer (N.dist x + 1))
    (hcard : (N.getLayer (N.dist x + 1)).card ≤ (N.getExtNbrs u x).card) :
    N.getLayer (N.dist x + 1) ⊆ N.G.N1 x := by
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro c hc
  rw [← heq] at hc
  exact mem_N1.2 (mem_exteriorNbrs.1 hc).2.2

/-- Port of `no_first_connected_back_arc`: a back arc into a parent that points to its whole next layer is a 2-cycle. -/
theorem no_back_arc_to_full_parent (hC : N.IsCounterexample) {v x : α}
    (hv : v ∈ N.getLayer (N.dist x + 1))
    (hlayer : N.getLayer (N.dist x + 1) ⊆ N.G.N1 x)
    (hvx : N.G.Adj v x) : False := by
  have hxv : N.G.Adj x v := mem_N1.1 (hlayer hv)
  have heq : v = x := hC.1.2 v x hvx hxv
  rw [heq] at hvx
  exact hC.1.1 x hvx.mem_vertices.1 hvx

lemma mem_getConnBacks {v x : α} :
    x ∈ N.getConnBacks v ↔ ∃ m, N.dist v = m + 1 ∧ x ∈ N.G.N1 v ∧ x ∈ N.getLayer m := by
  unfold getConnBacks
  rcases h : N.dist v with _ | m
  · constructor
    · intro hx
      simp at hx
    · rintro ⟨m, hm, -⟩
      omega
  · constructor
    · intro hx
      exact ⟨m, rfl, Finset.mem_inter.1 hx⟩
    · rintro ⟨m', hm', h1, h2⟩
      have hmm : m' = m := by omega
      subst hmm
      exact Finset.mem_inter.2 ⟨h1, h2⟩

lemma mem_layer_of_conn {v x : α} (hx : x ∈ N.getConnBacks v) :
    v ∈ N.getLayer (N.dist v) := by
  obtain ⟨m, hm, -, hxL⟩ := (N.mem_getConnBacks).1 hx
  have hlt := N.getLayer_index_lt_card hxL
  cases h : N.distOpt v with
  | none =>
    exfalso
    have hd : N.dist v = N.G.vertices.card + 1 := by simp [dist, h]
    omega
  | some n => exact N.mem_getLayer_dist h

/-- The `conn_case` node: with `points_next` as `hpoints`, the connected case is short. -/
theorem conn_case (hC : N.IsCounterexample) {v x : α} (hx : x ∈ N.getConnBacks v)
    (hpoints : N.getLayer (N.dist x + 1) ⊆ N.G.N1 x) : False := by
  obtain ⟨m, hm, hxv, hxL⟩ := (N.mem_getConnBacks).1 hx
  have hxd : N.dist x = m := N.dist_of_mem_getLayer hxL
  have hvL : v ∈ N.getLayer (N.dist x + 1) := by
    rw [hxd, ← hm]
    exact N.mem_layer_of_conn hx
  exact N.no_back_arc_to_full_parent hC hvL hpoints (mem_N1.1 hxv)

/-- Port of `interior_subset_layer`: with no back arcs at `v`, `int(u,v) ⊆ R_{n+1}`. -/
lemma interior_subset_layer {u v : α} {n : Nat} (hu : u ∈ N.getLayer n)
    (hback : N.G.N1 v ∩ N.getSeen (n + 1) = ∅) :
    N.getIntNbrs u v ⊆ N.getLayer (n + 1) := by
  intro x hx
  obtain ⟨-, hux, hvx⟩ := mem_interiorNbrs.1 hx
  have h1 : x ∈ N.getSeen (n + 1) ∪ N.getLayer (n + 1) :=
    N.N1_subset_seen_succ_succ hu (mem_N1.2 hux)
  have h2 : x ∉ N.getSeen (n + 1) := by
    intro hs
    have hx' : x ∈ N.G.N1 v ∩ N.getSeen (n + 1) := Finset.mem_inter.2 ⟨mem_N1.2 hvx, hs⟩
    rw [hback] at hx'
    simp at hx'
  exact (Finset.mem_union.1 h1).resolve_left h2

/-- Port of `interior_card_le_layer`; needs only `ShrinksLE`. -/
theorem interior_card_le_layer (hC : N.IsCounterexample) (hle : N.ShrinksLE)
    {u v : α} {n : Nat} (hu : u ∈ N.getLayer n) (hv : v ∈ N.getLayer (n + 1))
    (hback : N.G.N1 v ∩ N.getSeen (n + 1) = ∅) :
    (N.getIntNbrs u v).card ≤ N.delta - n - 1 := by
  have hsub : N.getIntNbrs u v ⊆ (N.getLayer (n + 1)).erase v := by
    intro c hc
    rw [Finset.mem_erase]
    refine ⟨?_, N.interior_subset_layer hu hback hc⟩
    intro hcv
    have hadj : N.G.Adj v c := (mem_interiorNbrs.1 hc).2.2
    rw [hcv] at hadj
    exact hC.1.1 v (N.getLayer_subset_vertices _ hv) hadj
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at hcard
  have hs := N.size_le_delta_sub hle n
  have h2 : N.size (n + 1) = (N.getLayer (n + 1)).card := rfl
  omega

/-- Port of `interior_degree_bounds`: `1 ≤ |int(u,v)| ≤ δ − 1` when `u` is δ-regular. -/
theorem interior_degree_bounds (hC : N.IsCounterexample) {u v : α}
    (hadj : N.G.Adj u v) (hreg : N.G.cardN1 u = N.delta) :
    1 ≤ (N.getIntNbrs u v).card ∧ (N.getIntNbrs u v).card ≤ N.delta - 1 := by
  have hu : u ∈ N.G.vertices := hadj.mem_vertices.1
  have hv : v ∈ N.G.vertices := hadj.mem_vertices.2
  constructor
  · have h1 := N.ext_card_lt_cardN1 (v := v) hC hu
    have hdeg := N.delta_le v hv
    have hpart : N.G.cardN1 v = (N.getIntNbrs u v).card + (N.getExtNbrs u v).card :=
      cardN1_eq_int_add_ext hC.1 hadj
    omega
  · have hsub : N.getIntNbrs u v ⊆ (N.G.N1 u).erase v := by
      intro c hc
      rw [Finset.mem_erase]
      refine ⟨?_, FiniteGraph.interiorNbrs_subset_N1 (G := N.G) u v hc⟩
      intro hcv
      have hcc : N.G.Adj v c := (mem_interiorNbrs.1 hc).2.2
      rw [hcv] at hcc
      exact hC.1.1 v hv hcc
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (mem_N1.2 hadj)] at hcard
    have h3 : (N.G.N1 u).card = N.delta := hreg
    omega

/-
/-- `interior_lb_node` with `hdeg` and `hv` both discharged. -/
theorem interior_lb_node (hC : N.IsCounterexample) {u v : α}
    (hfwd : N.IsForwardPair u v)
    (hext : (N.getExtNbrs u v).card ≤ N.delta - N.dist v)
    (hj : N.dist v ≤ N.delta) :
    N.dist v ≤ (N.getIntNbrs u v).card := by
  have hdeg := N.delta_le_of_adj hfwd.1
  have hpart : N.G.cardN1 v = (N.getIntNbrs u v).card + (N.getExtNbrs u v).card :=
    cardN1_eq_int_add_ext hC.1 hfwd.1
  omega
-/


/-- Non-Seymour at `u`, as a plain inequality. -/
lemma N2_lt_N1 (hC : N.IsCounterexample) {u : α} (hu : u ∈ N.G.vertices) :
    N.G.cardN2 u < N.G.cardN1 u := by
  simpa [FiniteGraph.isNonSeymour] using hC.2.2 u hu

/-- Non-Seymour replaces `hext`. `S` is a set of further second neighbours of `u`,
    disjoint from `E(u,v)`: this is what the doubling argument must provide. -/
theorem ext_le_of_nonSeymour (hC : N.IsCounterexample) {u v : α} {k : Nat}
    (hu : u ∈ N.G.vertices) (hreg : N.G.cardN1 u = N.delta)
    (S : Finset α) (hS : S ⊆ N.G.N2 u)
    (hdisj : Disjoint (N.getExtNbrs u v) S) (hk : k ≤ S.card) :
    (N.getExtNbrs u v).card ≤ N.delta - (k + 1) := by
  have h1 := N.N2_lt_N1 hC hu
  have hsub : N.getExtNbrs u v ∪ S ⊆ N.G.N2 u :=
    Finset.union_subset (N.G.exteriorNbrs_subset_N2 u v) hS
  have h2 : (N.getExtNbrs u v ∪ S).card ≤ N.G.cardN2 u := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h2
  omega

/-- `interior_lb_node` with `hext` replaced by non-Seymour at the parent. -/
theorem interior_lb_of_nonSeymour (hC : N.IsCounterexample) {u v : α}
    (hfwd : N.IsForwardPair u v) (hreg : N.G.cardN1 u = N.delta)
    (S : Finset α) (hS : S ⊆ N.G.N2 u)
    (hdisj : Disjoint (N.getExtNbrs u v) S)
    (hk : N.dist v ≤ S.card + 1) (hj : N.dist v ≤ N.delta) :
    N.dist v ≤ (N.getIntNbrs u v).card := by
  have hu : u ∈ N.G.vertices := hfwd.1.mem_vertices.1
  have hext := N.ext_le_of_nonSeymour hC (v := v) (k := N.dist v - 1) hu hreg S hS hdisj
    (by omega)
  have hdeg := N.delta_le_of_adj hfwd.1
  have hpart : N.G.cardN1 v = (N.getIntNbrs u v).card + (N.getExtNbrs u v).card :=
    cardN1_eq_int_add_ext hC.1 hfwd.1
  omega

/-- Ported from `no_minimum_layered_counterexample`: with the shrinking property and
    the interior-arc capacity bound (`hcap`, still to be proved), no layers survive. -/
theorem no_layered_counterexample (hirr : ¬ N.G.Adj N.root N.root) (hs : N.Shrinks)
    (hδ : 1 ≤ N.delta)
    (hcap : ∀ i, 1 ≤ i → i ≤ N.delta →
      2 * (N.size i * i) ≤ N.size i * N.size i - N.size i) :
    False :=
  N.layers_collapse_N hδ (N.size_formula_of_shrinks hirr hs) hcap

end NEGraph

end FiniteGraph

/-
===============================================================================
LEGACY CODE — NOT COMPILED
===============================================================================
Everything below was written against the old `GraphLevelOrder` design
(`\alpha`, `G.nodes`, `G.layerCoords`, `v.out_neighbors`, `fwdArc`, `Coord`, ...).
None of those definitions exist any more, so these theorems cannot compile as-is.
They are kept verbatim (inside this comment) so nothing is lost; port them onto
`NEGraph` one at a time and move them above.
Already ported: layer_size_all -> NEGraph.size_formula_of_shrinks,
layers_collapse_G -> NEGraph.layers_collapse_N,
no_minimum_layered_counterexample -> NEGraph.no_layered_counterexample,
layer_size_formula -> NEGraph.layer_size_formula.
===============================================================================
-- (A) old node-level partition / BFSWF / min-degree lemma / first layer_size_formula (lines 466-508)
/-- Node-level consistency: out-neighbors split into back / interior / exterior. -/
def PartitionWF (v : α) : Prop :=
  (G.outNeighbors v).card = (G.backNeighbors v).card + (G.interiorNbrs v).card + (G.exteriorNbrs v).card

def BFSWF : Prop :=
  ∀ v ∈ G.vertices, ∀ x ∈ G.outNeighbors v,
    (∃ d ∈ G.vertices, d = x) ∧ G.dist? x ≤ G.dist? v + 1

-- Prove once; downstream code uses only this lemma.
lemma IsMinOutDeg_of_minOutDegNode? (G : FiniteGraph) {u : Nat}
    (h : G.minOutDegNode? = some u) : G.IsMinOutDeg u := by
  -- 1. Unfold the definition to get it in terms of List.argmin
  have h_list : List.argmin (G.vertices.toList.filter () G.vertices.toList = some u := by
    simp [G.minOutDegNode?] at h
    exact h
  -- 2. Extract the three conjuncts (membership, minimality, tiebreaker)
  obtain ⟨h_mem_list, h_min, _⟩ := List.argmin_eq_some_iff.mp h_list
  -- 3. Bridge list membership back to finset membership
  have h_mem : u ∈ G.vertices := by
    rw [Finset.mem_to_list]
    exact h_mem_list
  exact ⟨h_mem, h_min⟩

theorem layer_size_formula
    (m : Nat) :
    (G.layerCoords (m + 2)).card = delta - (m + 1) := by
    let root := rootKey
  have h1 : (G.layerCoords 1).card = delta := by
    rw [h_layer1_eq, List.toFinset_card_of_nodup h_v0_nodup]
    exact h_v0_deg
  induction m with
  | zero =>
    have h2 := h_step 1 le_rfl
    rw [h1] at h2
    exact h2
  | succ m ih =>
    -- Suppose h_step applies to step m + 2, showing a decrement by 1 each step:
    have h_next := h_step (m + 2) (by omega)
    -- h_next likely looks like: (G.layerCoords (m + 3)).card = (G.layerCoords (m + 2)).card - 1
    rw [h_next, ih]
    -- Now the goal is: delta - (m + 1) - 1 = delta - (m + 1 + 1)
    -- omega handles this subtraction equality automatically:
    omega

-- (B) sketch referring to undefined SameChildren / NoBackArc / Doubling (lines 712-722)
theorem size_add_two_lt_cardN1 (hS : G.SameChildren r) {n u : α} -- n : Nat
    (hu : u ∈ G.layer r n) (hns : G.IsNonSeymour u) :
    (G.layer r (n + 2)).card < G.cardN1 u :=
  lt_of_le_of_lt (Finset.card_le_card (layer_add_two_subset_N2 hS hu)) hns

theorem size_le_pred (hB : G.NoBackArc r) (hS : G.SameChildren r)
    {n : Nat} {u : α} (hu : u ∈ G.layer r n) (hns : G.IsNonSeymour u)
    (hd : G.Doubling r n u) :
    (G.layer r (n + 2)).card ≤ (G.layer r (n + 1)).card - 1 := by
  have := layer_decrease hB hS hu hns hd
  omega

-- (C) everything written against the old GraphLevelOrder design (lines 769-1646)
lemma mem_exteriorNbrs {u v w : α} :
    w ∈ G.exteriorNbrs u v ↔
      G.Adj u v ∧ (((∃ x, G.Adj u x ∧ G.Adj x w) ∧ w ≠ u ∧ ¬ G.Adj u w) ∧ G.Adj v w) := by
  unfold exteriorNbrs
  split_ifs with h
  · simp [h, mem_N2]
  · simp [h]

theorem layer_size_formula
     (delta : Nat) (v0 : \alpha)
    (h_v0_deg : v0.out_neighbors.length = delta)
    (h_v0_nodup : v0.out_neighbors.Nodup)
    (h_layer1_eq : (G.layerCoords 1).card = v0.out_neighbors.toFinset.card)
    (h_step : ∀ j, 1 ≤ j →
      (G.layerCoords (j + 1)).card = (G.layerCoords j).card - 1)
    (m : Nat) :
    (G.layerCoords (m + 2)).card = delta - (m + 1) := by
  have h1 : (G.layerCoords 1).card = delta := by
    rw [h_layer1_eq, List.toFinset_card_of_nodup h_v0_nodup]
    exact h_v0_deg
  induction m with
  | zero =>
    have h2 := h_step 1 le_rfl
    rw [h1] at h2
    exact h2
  | succ m ih =>
    have h_next := h_step (m + 2) (by omega)
    show (G.layerCoords (m + 3)).card = delta - (m + 1 + 1)
    rw [h_next, ih]
    omega

theorem interior_degree_lower_bound_of_mce

    (mce : G.IsMinimumCounterexample)
    (k : ℕ)
    (u vk : \alpha)
    (hk_layer : vk.dist = k + 1)
    (h_layer_sizes : ∀ i, i ≤ G.max_layer → (G.layerCoords i).card = G.delta - i + 1)
    (h_no_back : G.NoBackArcs) :
    vk.interior_neighbors.length = k + 1 := by
  by_contra h_contra
  push_neg at h_contra -- vk.interior_neighbors.length > k + 1

  -- 1. Obtain a redundant/removable interior neighbor coordinate c
  -- Since length > k + 1 and layer-size / degree bounds dictate the maximum
  -- allowable interior neighbors, an excess neighbor can be extracted.
  have h_excess : vk.interior_neighbors.length ≥ k + 2 := h_contra

  -- Assuming you have a helper lemma to extract an element when length exceeds the bound:
  obtain ⟨c, hc_mem, hc_redundant⟩ := GraphLevelOrder.exists_removable_interior_neighbor vk h_excess h_layer_sizes

  let x := vk.toCoords

  -- 2. Prove that removing this arc strictly decreases the interior arc count
  have h_lt : interiorArcCount (G.removeArc x c) < interiorArcCount G := by
    apply mceMetric_lt_of_arcCount_lt  -- or your specific metric drop lemma
    exact GraphLevelOrder.interiorArcCount_decreases_of_removeArc G x c hc_mem hc_redundant

  -- 3. Prove that the modified graph is still a valid counterexample
  have h_cex : IsCounterexample (G.removeArc x c) := by
    constructor
    · -- Verify degree and anti-Seymour properties are preserved
      apply GraphLevelOrder.preserve_counterexample_of_removable_interior
      · exact mce.property
      · exact hc_redundant
    · -- Verify layer-size constraints remain satisfied
      intro i hi
      exact h_layer_sizes i hi

  -- 4. Contradict the minimality of G
  exact not_mce_of_removable x c h_lt h_cex mce

theorem fwdArc_spec  (u v : \alpha) :
    fwdArc G u v = true ↔
      u ∈ G.nodes ∧ v ∈ G.nodes ∧ v.toCoords ∈ u.out_neighbors
        ∧ v.dist = u.dist + 1 := by
  unfold fwdArc
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨hu, hv⟩, huv⟩, hd⟩
    exact ⟨Array.mem_of_contains_eq_true hu, Array.mem_of_contains_eq_true hv,
      List.mem_of_elem_eq_true huv, hd⟩
  · rintro ⟨hu, hv, huv, hd⟩
    exact ⟨⟨⟨Array.contains_eq_true_of_mem hu, Array.contains_eq_true_of_mem hv⟩,
      List.elem_eq_true_of_mem huv⟩, hd⟩

theorem exteriorNeighbors_subset_layer
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (u v : \alpha) (hfwd : fwdArc G u v = true)
    (hnb : G.backNeighbors u v = ∅)
    (hsame : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors) :
    G.exteriorNeighbors u v ⊆ G.layerCoords (v.dist + 1) := by
  obtain ⟨hu_mem, hv_mem, _, hd⟩ := (fwdArc_spec G u v).mp hfwd
  intro x hx
  have hguard : (G.nodes.contains u && G.nodes.contains v
      && v.dist == u.dist + 1) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨Array.contains_eq_true_of_mem hu_mem,
            Array.contains_eq_true_of_mem hv_mem⟩, hd⟩
  unfold exteriorNeighbors at hx
  rw [hguard] at hx
  obtain ⟨hN2, hxv⟩ := Finset.mem_inter.mp hx
  have hxv' : x ∈ v.out_neighbors := List.mem_toFinset.mp hxv
  -- x ∉ N1(u) = out(u)
  have hnotu : x ∉ u.out_neighbors := by
    have h := (Finset.mem_filter.mp hN2).2.2        -- x ∉ getN1Finset G u.toCoords
    rw [getN1Finset_eq G hu u hu_mem] at h
    simpa using h
  -- layer bounds
  have hle := (hw v hv_mem x hxv').2
  have hge : v.dist ≤ x.1 := by
    by_contra hlt
    have : x ∈ G.backNeighbors u v := by
      unfold backNeighbors; rw [hguard]
      simp [hxv', Nat.lt_of_not_le hlt]
    rw [hnb] at this; simp at this
  have hlay : x.1 = v.dist + 1 := by
    rcases Nat.lt_or_ge v.dist x.1 with h | h
    · omega
    · exact absurd (hsame x hxv' (by omega)) hnotu
  obtain ⟨⟨d, hd_mem, hd_eq⟩, _⟩ := hw v hv_mem x hxv'
  have hdd : d.dist = x.1 := by rw [← hd_eq]; rfl
  simp only [layerCoords, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨d, ⟨Array.mem_def.mp hd_mem, by omega⟩, hd_eq⟩

theorem exterior_card_le_layer_formula
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (u v : \alpha) (k : Nat)
    (hfwd : fwdArc G u v = true)
    (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hsame : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors)
    (hlayer : (G.layerCoords (k + 2)).card = G.delta - (k + 1)) :
    (G.exteriorNeighbors u v).card ≤ G.delta - (k + 1) := by
  have hsub := exteriorNeighbors_subset_layer G hu hw u v hfwd hnb hsame
  rw [hk] at hsub
  exact hsub |> Finset.card_le_card |>.trans hlayer.le

theorem maxInDeg_eq_one_iff_bijective {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) :
    (∀ y, (Finset.univ.filter (fun x => f x = y)).card ≤ 1) ↔ Function.Bijective f := by
  rw [← Finite.injective_iff_bijective]
  constructor
  · intro h x x' hxx'
    by_contra hne
    have h2 : 1 < (Finset.univ.filter (fun z => f z = f x)).card := by
      rw [Finset.one_lt_card]
      exact ⟨x, by simp, x', by simp [hxx'.symm], hne⟩
    have := h (f x)
    omega
  · intro hinj y
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp at ha hb
    exact hinj (ha.trans hb.symm)

theorem interior_lb_node
    (v : \alpha) (δ k : Nat)
    (hPart : PartitionWF v)
    (hdeg : δ ≤ v.out_neighbors.length)
    (hback0 : v.back_neighbors.length = 0)
    (hext : v.exterior_neighbors.length ≤ δ - (k + 1))
    (hk_le : k + 1 ≤ δ) :
    k + 1 ≤ v.interior_neighbors.length := by
  unfold PartitionWF at hPart
  omega

/-- The BFS layer structure the distance formula needs. -/
structure LayerShrink  (v0 : \alpha) : Prop where
  deg    : v0.out_neighbors.length = G.delta
  nodup  : v0.out_neighbors.Nodup
  layer1 : (G.layerCoords 1).card = v0.out_neighbors.toFinset.card
  step   : ∀ j, 1 ≤ j → (G.layerCoords (j + 1)).card = (G.layerCoords j).card - 1

theorem LayerShrink.card_formula {G : GraphLevelOrder} {v0 : \alpha}
    (h : LayerShrink G v0) (m : Nat) :
    (G.layerCoords (m + 2)).card = G.delta - (m + 1) :=
  layer_size_formula G G.delta v0 h.deg h.nodup h.layer1 h.step m

theorem exterior_len_le
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (u v v0 : \alpha) (k : Nat)
    (hL : LayerShrink G v0)
    (hfwd : fwdArc G u v = true) (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hsame : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors)
    (hext_len : v.exterior_neighbors.length = (G.exteriorNeighbors u v).card) :
    v.exterior_neighbors.length ≤ G.delta - (k + 1) := by
  rw [hext_len]
  exact exterior_card_le_layer_formula G hu hw u v k hfwd hk hnb hsame
    (hL.card_formula k)

theorem interior_degree_lower_bound
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (u v v0 : \alpha) (k : Nat)
    (hL : LayerShrink G v0)
    (hfwd : fwdArc G u v = true) (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hsame : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors)
    (h_min : ∀ x ∈ G.nodes.toList, G.delta ≤ x.out_neighbors.length)
    (hPart : PartitionWF v) (hback0 : v.back_neighbors.length = 0)
    (hext_len : v.exterior_neighbors.length = (G.exteriorNeighbors u v).card)
    (hk_le : k + 1 ≤ G.delta) :
    k + 1 ≤ v.interior_neighbors.length := by
  obtain ⟨_, hv_mem, _, _⟩ := (fwdArc_spec G u v).mp hfwd
  have hv_in : v ∈ G.nodes.toList := Array.mem_toList_iff.mpr hv_mem
  exact interior_lb_node v G.delta k hPart
    (node_out_degree_ge_delta G v hv_in G.delta h_min)
    hback0
    (exterior_len_le G hu hw u v v0 k hL hfwd hk hnb hsame hext_len)
    hk_le

theorem interior_degree_rigidity_old
  (k : Nat)
  -- Suppose we have a quantity representing the interior neighbor count / degree of u
  -- (e.g., sum of sizes of interiorNeighbors with forward children)
  (int_count : Nat)
  -- Hypotheses representing your MCE constraints:
  (h_not_too_low : int_count < k → False) -- Too low forces another forward arc / violates structure
  (h_not_too_high : k < int_count → False) -- Too high violates MCE conditions / non-Seymour bounds
  : int_count = k := by
  -- Trichotomy: either int_count < k, int_count = k, or int_count > k
  rcases lt_trichotomy int_count k with h_lt | h_eq | h_gt
  · -- Case 1: int_count < k (Too low)
    exfalso
    exact h_not_too_low h_lt
  · -- Case 2: int_count = k (The exact target equality)
    exact h_eq
  · -- Case 3: int_count > k (Too high)
    exfalso
    exact h_not_too_high h_gt

theorem node_interior_degree_eq_k_old
  (k : Nat)
  -- Let's say int_deg is the total interior neighbors in layer k+1
  (int_deg : Nat)
  (h_lower_bound : k ≤ int_deg) -- Derived from min-degree / no-back-arcs
  (h_upper_bound : int_deg ≤ k) -- Derived from non-Seymour / MCE constraints
  : int_deg = k := by
  omega
/-
-------------------------------------------------------------------------------
--Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/

-- /-- Two nodes u and v are connected by a back-path/arc if there is a node x
--     in v's back-neighbors that is also an out-neighbor of u. -/
def ConnectedBack  (u v : \alpha) : Prop :=
  ∃ x ∈ G.backNeighbors u v, x ∈ u.out_neighbors

-- /-- A graph has no connected back-arcs if no forward arc
--     coexists with a connected back-arc structure. -/
def NoConnectedBack  : Prop :=
  ∀ u v, fwdArc G u v = true → ¬ ConnectedBack G u v

def IsRoot  (r : \alpha) : Prop :=
  r ∈ G.nodes ∧ ∀ n ∈ G.nodes, n ≠ r → \alpha.Lt r n

theorem root_unique  (r₁ r₂ : \alpha)
    (h1 : IsRoot G r₁) (h2 : IsRoot G r₂) : r₁ = r₂ := by
  by_contra hne
  have a := h1.2 r₂ h2.1 (Ne.symm hne)   -- Lt r₁ r₂
  have b := h2.2 r₁ h1.1 hne             -- Lt r₂ r₁
  unfold \alpha.Lt at a b
  omega

/-- The least node sits in layer 0, provided layer 0 is nonempty. -/
theorem root_dist_zero  (r : \alpha) (hr : IsRoot G r)
    (h0 : ∃ n ∈ G.nodes, n.dist = 0) : r.dist = 0 := by
  obtain ⟨n, hn, hn0⟩ := h0
  by_cases h : n = r
  · subst h; exact hn0
  · have := hr.2 n hn h
    unfold \alpha.Lt at this
    omega

theorem layer_bound_of_step (s : Nat → Nat) (δ : Nat)
    (h1 : s 1 = δ) (hstep : ∀ j, 1 ≤ j → s (j + 1) ≤ s j - 1) :
    ∀ m, s (m + 2) ≤ δ - (m + 1) := by
  intro m
  induction m with
  | zero =>
    have h : s 2 ≤ s 1 - 1 := hstep 1 le_rfl
    show s 2 ≤ δ - (0 + 1)
    omega
  | succ m ih =>
    have h : s (m + 3) ≤ s (m + 2) - 1 := hstep (m + 2) (by omega)
    show s (m + 3) ≤ δ - (m + 1 + 1)
    omega

def layerIds  (j : Nat) : Finset Nat :=
  ((G.nodes.filter (·.dist == j)).toList.map (·.lexId)).toFinset

/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/

def IsMinOutDeg  (δ : Nat) : Prop :=
  (∀ x ∈ G.graph.vertices, δ ≤ G.graph.cardN1 x) ∧
  (∃ x ∈ G.graph.vertices, G.graph.cardN1 x = δ)

def NoBackArcs  : Prop :=
  ∀ v ∈ G.nodes, ∀ u ∈ G.nodes, G.backNeighbors u v = ∅

theorem interior_lower_bound (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hback : backC = 0)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    k + 1 ≤ intC := by omega

/-- Back arcs forced by interior deficiency (no load balance, no minimality). -/
theorem back_ge_deficiency (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ) :
    (k + 1) - intC ≤ backC := by omega

theorem too_few_interior_old (δ k intC extC backC outC : Nat)
    (hout : δ ≤ outC) (hsplit : outC = backC + intC + extC)
    (hlayer : extC ≤ δ - (k + 1)) (hk : k + 1 ≤ δ)
    (hdef : intC < k + 1) : 0 < backC := by omega

theorem layers_disjoint
    (k1 k2 : Nat) (v_k1 v_k2 : \alpha)
    (h_dist1 : v_k1.dist = k1) (h_dist2 : v_k2.dist = k2)
    (h_neq : k1 ≠ k2) : v_k1 ≠ v_k2 := by
  intro h_eq
  apply h_neq
  rw [← h_dist1, ← h_dist2, h_eq]

theorem layerCoords_disjoint
    (j₁ j₂ : Nat) (hne : j₁ ≠ j₂) :
    Disjoint (G.layerCoords j₁) (G.layerCoords j₂) := by
  rw [Finset.disjoint_left]
  intro c h1 h2
  simp only [GraphLevelOrder.layerCoords, List.mem_toFinset, List.mem_map, List.mem_filter,
    beq_iff_eq] at h1 h2
  obtain ⟨a, ⟨_, ha⟩, rfl⟩ := h1
  obtain ⟨b, ⟨_, hb⟩, hab⟩ := h2
  -- hab : b.toCoords = a.toCoords, so b.dist = a.dist
  have : b.dist = a.dist := congrArg Prod.fst hab
  omega

theorem interior_ge_of_layers
    (out A B : Finset Coord) (delta k : Nat)
    (hdeg : delta ≤ out.card)
    (hsub : out ⊆ A ∪ B)            -- BFS + no back arcs: A = R_k, B = R_{k+1}
    (hB : B.card ≤ delta - k)       -- from the layer formula
    (hk : k ≤ delta) :
    k ≤ (out ∩ A).card := by
  have h1 : out ⊆ (out ∩ A) ∪ B := by
    intro x hx
    rcases Finset.mem_union.mp (hsub hx) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, h⟩)
    · exact Finset.mem_union_right _ h
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  omega

lemma child_interior_deficit
    (child : \alpha) (k : Nat)
    (h_part : PartitionWF child)
    (h_deg : k ≤ child.out_neighbors.length)
    (h_int : child.interior_neighbors.length < k) :
    0 < child.back_neighbors.length ∨ 0 < child.exterior_neighbors.length := by
  unfold PartitionWF at h_part
  omega

/-
-------------------------------------------------------------------------------
--Stage 5: Minimum Counterexample Structure
-------------------------------------------------------------------------------
-/
/-- Case 1: the first irregular child of a parent at distance k cannot exist. -/

theorem out_eq_int_union_ext
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (k : Nat) (u v : \alpha)
    (hfwd : fwdArc G u v = true)
    (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hno_same : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors) :
    v.out_neighbors.toFinset
      = G.interiorNeighbors u v ∪ G.exteriorNeighbors u v := by
  obtain ⟨hu_node, hv_node, hadj, hdist⟩ := (fwdArc_spec G u v).mp hfwd
  -- hadj : v.toCoords ∈ u.out_neighbors  (shape assumed from fwdArc_spec)
  have hcond : (G.nodes.contains u && G.nodes.contains v
                && v.dist == u.dist + 1) = true := by
    simp [hu_node, hv_node, hdist]        -- Array.contains lemma names are version-sensitive
  ext x
  constructor
  · intro hx
    have hxv : x ∈ v.out_neighbors := List.mem_toFinset.mp hx
    have hle := (hw v hv_node x hxv).2
    -- no back arcs: x is not below v's layer
    have hge : v.dist ≤ x.1 := by
      by_contra hlt
      have : x ∈ G.backNeighbors u v := by
        unfold GraphLevelOrder.backNeighbors
        rw [hcond]
        simp [hxv]; omega
      rw [hnb] at this; simp at this
    by_cases heq : x.1 = v.dist
    · -- same layer as v: interior
      apply Finset.mem_union_left
      unfold GraphLevelOrder.interiorNeighbors
      rw [hcond]
      simp [hxv, hno_same x hxv heq]
    · -- layer v.dist + 1: exterior
      apply Finset.mem_union_right
      unfold GraphLevelOrder.exteriorNeighbors
      rw [hcond]
      refine Finset.mem_inter.mpr ⟨?_, by simpa using hxv⟩
      have hx2 : x.1 = u.dist + 2 := by omega
      unfold GraphLevelOrder.getN2Finset
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      refine ⟨⟨v.toCoords, ?_, ?_⟩, ?_, ?_⟩
      · rw [GraphLevelOrder.getN1Finset_eq G hu u hu_node]; simpa using hadj
      · rw [GraphLevelOrder.getN1Finset_eq G hu v hv_node]; simpa using hxv
      · intro h; have := congrArg Prod.fst h; simp [\alpha.toCoords] at this; omega
      · rw [GraphLevelOrder.getN1Finset_eq G hu u hu_node]
        intro hmem
        have := (hw u hu_node x (List.mem_toFinset.mp hmem)).2
        omega
  · intro hx
    rcases Finset.mem_union.mp hx with h | h
    · unfold GraphLevelOrder.interiorNeighbors at h
      rw [hcond] at h
      exact (Finset.mem_inter.mp h).2
    · unfold GraphLevelOrder.exteriorNeighbors at h
      rw [hcond] at h
      exact (Finset.mem_inter.mp h).2

theorem int_ext_disjoint  (hu : G.CoordUnique)
    (u v : \alpha) (hu_node : u ∈ G.nodes) :
    Disjoint (G.interiorNeighbors u v) (G.exteriorNeighbors u v) := by
  rw [Finset.disjoint_left]
  intro x hxi hxe
  by_cases hc : (G.nodes.contains u && G.nodes.contains v
                  && v.dist == u.dist + 1) = true
  · rw [interiorNeighbors, hc] at hxi
    rw [exteriorNeighbors, hc] at hxe
    have h1 : x ∈ u.out_neighbors.toFinset := (Finset.mem_inter.mp hxi).1
    have h2 := (Finset.mem_inter.mp hxe).1
    unfold getN2Finset at h2
    simp only [Finset.mem_filter] at h2
    rw [getN1Finset_eq G hu u hu_node] at h2
    exact h2.2.2 h1
  · rw [interiorNeighbors, if_neg hc] at hxi
    simp at hxi

theorem cond_of_nodes {G : GraphLevelOrder} {u v : \alpha}
    (hu : u ∈ G.nodes) (hv : v ∈ G.nodes) (hd : v.dist = u.dist + 1) :
    (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true := by
  simp [hu, hv, hd]

theorem extra_forward_arc_produces_seymour_vertex
     (u v : \alpha)
    (hfwd : fwdArc G u v = true)
    (h_ext_bound : G.cardN1 u.toCoords ≤ (G.exteriorNeighbors u v).card) :
    G.cardN1 u.toCoords ≤ G.cardN2 u.toCoords := by
  obtain ⟨hu_mem, hv_mem, _, hd⟩ := (fwdArc_spec G u v).mp hfwd
  have h_cond := cond_of_nodes hu_mem hv_mem hd
  exact h_ext_bound.trans (Finset.card_le_card
    (fun c hc => exterior_neighbor_implies_second_neighbor G u v c h_cond hc))

/-- A counterexample G with fewer/excess arcs breaking minimality
    contradicts the Minimum Counterexample H. -/
theorem extra_interior_violates_mce_metric
    (G H : GraphLevelOrder)
    (h_mce : IsMinimumCounterexample H)
    (h_G_counter : IsCounterexample G)
    (h_smaller_metric : mceMetric G < mceMetric H) :
    False := by
  obtain ⟨_, h_min⟩ := h_mce
  have h_le : mceMetric H ≤ mceMetric G := h_min G h_G_counter
  exact absurd h_smaller_metric (not_lt_of_ge h_le)

theorem out_length_eq_int_add_ext
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (k : Nat) (u v : \alpha)
    (hfwd : fwdArc G u v = true) (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hno_same : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors)
    (hnd : v.out_neighbors.Nodup) :
    v.out_neighbors.length
      = (G.interiorNeighbors u v).card + (G.exteriorNeighbors u v).card := by
  obtain ⟨hu_node, _, _, _⟩ := (fwdArc_spec G u v).mp hfwd
  rw [← List.toFinset_card_of_nodup hnd,
      out_eq_int_union_ext G hu hw k u v hfwd hk hnb hno_same]
  exact Finset.card_union_of_disjoint (int_ext_disjoint G hu u v hu_node)

theorem interior_eq_of_tight
     (hu : G.CoordUnique) (hw : G.BFSWF)
    (u v : \alpha) (k : Nat)
    (hfwd : fwdArc G u v = true) (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅)
    (hno_same : ∀ x ∈ v.out_neighbors, x.1 = v.dist → x ∈ u.out_neighbors)
    (hnd : v.out_neighbors.Nodup)
    (hdeg : v.out_neighbors.length = G.delta)
    (hext_tight : (G.exteriorNeighbors u v).card = G.delta - (k + 1))
    (hk_le : k + 1 ≤ G.delta) :
    (G.interiorNeighbors u v).card = k + 1 := by
  have h := out_length_eq_int_add_ext G hu hw k u v hfwd hk hnb hno_same hnd
  omega

theorem int_not_too_low
    (δ k int_d fwd_d back_d : Nat)
    (h_deg   : δ ≤ int_d + fwd_d + back_d)   -- out-degree ≥ δ
    (h_noback : back_d = 0)
    (h_case1 : fwd_d + k ≤ δ)                -- case 1: no extra forward arcs
    : ¬ int_d < k := by
  intro h_low
  omega

lemma child_interior_deficit_no_back

    (child : \alpha) (k : Nat)
    (h_part : PartitionWF child)
    (h_deg : G.delta ≤ child.out_neighbors.length)
    (h_no_back : child.back_neighbors.length = 0)
    (h_int : child.interior_neighbors.length < k) :
    G.delta < child.exterior_neighbors.length + k := by
  unfold PartitionWF at h_part
  omega

theorem fewer_interior_implies_extra_forward
     (u v : \alpha)
    (h_cond : (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true)
    (h_ext_bound : G.cardN1 u.toCoords ≤ (G.exteriorNeighbors u v).card) :
    G.cardN1 u.toCoords ≤ G.cardN2 u.toCoords := by
  -- 1. Show exteriorNeighbors G u v is a subset of getN2Finset G u.toCoords
  have h_sub : G.exteriorNeighbors u v ⊆ G.getN2Finset u.toCoords := by
    intro c hc
    exact exterior_neighbor_implies_second_neighbor G u v c h_cond hc

  -- 2. Take cardinalities: |exteriorNeighbors| <= |N2(u)|
  have h_card_le := Finset.card_le_card h_sub

  -- 3. Chain inequalities: |N1(u)| <= |exteriorNeighbors| <= |N2(u)|
  exact h_ext_bound.trans h_card_le

theorem interior_degree_bounds
     (u v : \alpha)
    (h_cond : (G.nodes.contains u && G.nodes.contains v && v.dist == u.dist + 1) = true)
    (hu_deg : G.cardN1 u.toCoords = G.delta)
    (h_no_seymour_u : G.cardN2 u.toCoords < G.cardN1 u.toCoords)
    (hcard1 : G.cardN1 u.toCoords = u.out_neighbors.toFinset.card)
    (hv_deg : G.delta ≤ v.out_neighbors.toFinset.card)
    (hv_in : v.toCoords ∈ u.out_neighbors.toFinset)          -- from fwdArc G u v
    (hv_noloop : v.toCoords ∉ v.out_neighbors.toFinset)       -- no loops
    (hv_cover : v.out_neighbors.toFinset ⊆
        interiorNeighbors G u v ∪ exteriorNeighbors G u v) :  -- N2 definition + oriented
    1 ≤ (interiorNeighbors G u v).card ∧
    (interiorNeighbors G u v).card ≤ G.delta - 1 := by
  have h_ext_le : (exteriorNeighbors G u v).card ≤ G.cardN2 u.toCoords :=
    Finset.card_le_card (fun c hc =>
      exterior_neighbor_implies_second_neighbor G u v c h_cond hc)
  have h_union : v.out_neighbors.toFinset.card ≤
      (interiorNeighbors G u v).card + (exteriorNeighbors G u v).card :=
    (Finset.card_le_card hv_cover).trans (Finset.card_union_le _ _)
  constructor
  · omega
  · have hsub : interiorNeighbors G u v ⊆ u.out_neighbors.toFinset.erase v.toCoords := by
      intro c hc
      have hc' : c ∈ u.out_neighbors.toFinset ∩ v.out_neighbors.toFinset := by
        unfold interiorNeighbors at hc
        rw [h_cond] at hc
        exact hc
      rw [Finset.mem_inter] at hc'
      rw [Finset.mem_erase]
      exact ⟨fun h => hv_noloop (h ▸ hc'.2), hc'.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hv_in] at this
    omega

theorem mem_getN2Finset_iff  (c x : Coord) :
    x ∈ getN2Finset G c ↔
      (∃ a ∈ getN1Finset G c, x ∈ getN1Finset G a)
        ∧ x ≠ c ∧ x ∉ getN1Finset G c := by
  simp only [getN2Finset, Finset.mem_filter, Finset.mem_biUnion]

theorem out_subset_int_union_ext_general
     (hu : G.CoordUnique)
    (u v : \alpha) (hu_node : u ∈ G.nodes) (hv_node : v ∈ G.nodes)
    (hadj : v.toCoords ∈ u.out_neighbors)
    (hd : v.dist = u.dist + 1)
    (h_anti : u.toCoords ∉ v.out_neighbors) :
    v.out_neighbors.toFinset
      ⊆ G.interiorNeighbors u v ∪ G.exteriorNeighbors u v := by
  have hc := cond_of_nodes hu_node hv_node hd
  intro x hx
  have hxv : x ∈ v.out_neighbors := List.mem_toFinset.mp hx
  by_cases hxu : x ∈ u.out_neighbors
  · apply Finset.mem_union_left
    rw [interiorNeighbors, hc]
    exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hxu, hx⟩
  · apply Finset.mem_union_right
    rw [exteriorNeighbors, hc]
    refine Finset.mem_inter.mpr ⟨?_, hx⟩
    rw [mem_getN2Finset_iff, getN1Finset_eq G hu u hu_node]
    refine ⟨⟨v.toCoords, List.mem_toFinset.mpr hadj, ?_⟩, ?_, ?_⟩
    · rw [getN1Finset_eq G hu v hv_node]; exact hx
    · intro h; exact h_anti (h ▸ hxv)
    · exact fun hmem => hxu (List.mem_toFinset.mp hmem)

theorem out_length_le_int_add_ext_general
     (hu : G.CoordUnique)
    (u v : \alpha) (hu_node : u ∈ G.nodes) (hv_node : v ∈ G.nodes)
    (hadj : v.toCoords ∈ u.out_neighbors) (hd : v.dist = u.dist + 1)
    (h_anti : u.toCoords ∉ v.out_neighbors)
    (hnd : v.out_neighbors.Nodup) :
    v.out_neighbors.length
      ≤ (G.interiorNeighbors u v).card + (G.exteriorNeighbors u v).card := by
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card
    (out_subset_int_union_ext_general G hu u v hu_node hv_node hadj hd h_anti)).trans
    (Finset.card_union_le _ _)

theorem chain_ends_measure {α : Type*} (μ : α → Nat) (P Closes : α → Prop)
    (h0 : ∃ a, P a)
    (hstep : ∀ a, P a → Closes a ∨ ∃ b, P b ∧ μ b < μ a) :
    ∃ a, P a ∧ Closes a := by
  obtain ⟨a, ha, hmin⟩ :=
    (InvImage.wf μ wellFounded_lt).has_min {a | P a} h0
  rcases hstep a ha with hc | ⟨b, hb, hlt⟩
  · exact ⟨a, ha, hc⟩
  · exact absurd hlt (hmin b hb)

/-- Branch 1: no overlap between N⁺(b) and N⁺(a) makes `a` Seymour. -/
theorem seymour_of_disconnected_back_arc
     (hu : G.CoordUnique)
    (a b : \alpha) (ha : a ∈ G.nodes) (hb : b ∈ G.nodes)
    (hback : b.toCoords ∈ a.out_neighbors)
    (h_anti : a.toCoords ∉ b.out_neighbors)
    (h_disc : ∀ z ∈ b.out_neighbors, z ∉ a.out_neighbors)
    (hbnd : b.out_neighbors.Nodup)
    (hreg : a.out_neighbors.length ≤ G.delta)
    (hmin : G.delta ≤ b.out_neighbors.length) :
    G.cardN1 a.toCoords ≤ G.cardN2 a.toCoords := by
  have h1 : G.cardN1 a.toCoords ≤ a.out_neighbors.length := by
    unfold cardN1
    rw [getN1Finset_eq G hu a ha]
    exact List.toFinset_card_le _
  have h2 : b.out_neighbors.length = b.out_neighbors.toFinset.card :=
    (List.toFinset_card_of_nodup hbnd).symm
  have h3 : b.out_neighbors.toFinset ⊆ getN2Finset G a.toCoords := by
    intro x hx
    have hxb := List.mem_toFinset.mp hx
    rw [mem_getN2Finset_iff, getN1Finset_eq G hu a ha]
    refine ⟨⟨b.toCoords, List.mem_toFinset.mpr hback, ?_⟩, ?_, ?_⟩
    · rw [getN1Finset_eq G hu b hb]; exact hx
    · intro h; exact h_anti (h ▸ hxb)
    · exact fun hmem => h_disc x hxb (List.mem_toFinset.mp hmem)
  have h4 := Finset.card_le_card h3
  unfold cardN2
  omega

/-- Disconnected back arcs cannot exist in a counterexample.
    `hpath` is branch 2, stated as a stake. -/
theorem no_disconnected_back_arc
     (hu : G.CoordUnique)
    (hall : ∀ x ∈ G.nodes, ¬ (G.cardN1 x.toCoords ≤ G.cardN2 x.toCoords))
    (a b : \alpha) (ha : a ∈ G.nodes) (hb : b ∈ G.nodes)
    (hback : b.toCoords ∈ a.out_neighbors)
    (h_anti : a.toCoords ∉ b.out_neighbors)
    (hbnd : b.out_neighbors.Nodup)
    (hreg : a.out_neighbors.length ≤ G.delta)
    (hmin : G.delta ≤ b.out_neighbors.length)
    (hpath : (∃ z ∈ b.out_neighbors, z ∈ a.out_neighbors) →
        ∃ x ∈ G.nodes, G.cardN1 x.toCoords ≤ G.cardN2 x.toCoords) :
    False := by
  by_cases hint : ∃ z ∈ b.out_neighbors, z ∈ a.out_neighbors
  · obtain ⟨x, hx, hle⟩ := hpath hint
    exact hall x hx hle
  · push_neg at hint
    exact hall a ha
      (seymour_of_disconnected_back_arc G hu a b ha hb hback h_anti hint hbnd hreg hmin)


/-- Every vertex of R_{k+1} is an out-neighbor of x, when the exterior is tight. -/
theorem layer_succ_subset_out
     (u' x : \alpha)
    (hext_sub : G.exteriorNeighbors u' x ⊆ G.layerCoords (x.dist + 1))
    (hcard : (G.layerCoords (x.dist + 1)).card ≤ (G.exteriorNeighbors u' x).card) :
    G.layerCoords (x.dist + 1) ⊆ x.out_neighbors.toFinset := by
  have heq := Finset.eq_of_subset_of_card_le hext_sub hcard
  intro c hc
  rw [← heq] at hc
  unfold exteriorNeighbors at hc
  by_cases hcond : (G.nodes.contains u' && G.nodes.contains x
                      && x.dist == u'.dist + 1) = true
  · rw [hcond] at hc
    exact (Finset.mem_inter.mp hc).2
  · rw [if_neg hcond] at hc
    simp at hc

theorem mem_layerCoords_of_node  (v : \alpha) (j : Nat)
    (hv : v ∈ G.nodes) (hj : v.dist = j) :
    v.toCoords ∈ G.layerCoords j := by
  show v.toCoords ∈
    ((G.nodes.toList.filter (·.dist == j)).map (·.toCoords)).toFinset
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr
      ⟨v, List.mem_filter.mpr ⟨Array.mem_toList_iff.mpr hv, by simp [hj]⟩, rfl⟩)

theorem no_first_connected_back_arc
     (v x : \alpha)
    (hv_node : v ∈ G.nodes)
    (hxdist : x.dist + 1 = v.dist)
    (hxv : x.toCoords ∈ v.out_neighbors)
    (hlayer : G.layerCoords (x.dist + 1) ⊆ x.out_neighbors.toFinset)
    (hanti : v.toCoords ∈ x.out_neighbors → x.toCoords ∉ v.out_neighbors) :
    False := by
  have hvmem : v.toCoords ∈ G.layerCoords (x.dist + 1) :=
    mem_layerCoords_of_node G v _ hv_node hxdist.symm
  exact hanti (List.mem_toFinset.mp (hlayer hvmem)) hxv

theorem interior_subset_layer  (hw : G.BFSWF)
    (u v : \alpha) (hu_node : u ∈ G.nodes) (hv_node : v ∈ G.nodes)
    (hd : v.dist = u.dist + 1) (hnb : G.backNeighbors u v = ∅) :
    G.interiorNeighbors u v ⊆ G.layerCoords v.dist := by
  have hc := cond_of_nodes hu_node hv_node hd
  intro x hx
  rw [interiorNeighbors, hc] at hx
  obtain ⟨hxu, hxv⟩ := Finset.mem_inter.mp hx
  have hle : x.1 ≤ u.dist + 1 := (hw u hu_node x (List.mem_toFinset.mp hxu)).2
  have hge : v.dist ≤ x.1 := by
    by_contra hlt
    push_neg at hlt
    have hb : x ∈ G.backNeighbors u v := by
      rw [backNeighbors, hc]
      exact Finset.mem_filter.mpr ⟨hxv, hlt⟩
    rw [hnb] at hb
    simp at hb
  obtain ⟨⟨d, hd_mem, hd_eq⟩, _⟩ := hw v hv_node x (List.mem_toFinset.mp hxv)
  have hdd : d.dist = x.1 := by rw [← hd_eq]; rfl
  rw [← hd_eq]
  exact mem_layerCoords_of_node G d _ hd_mem (by omega)

theorem LayerShrink.card_succ {G : GraphLevelOrder} {v0 : \alpha}
    (h : LayerShrink G v0) (k : Nat) :
    (G.layerCoords (k + 1)).card = G.delta - k := by
  cases k with
  | zero =>
    have h1 : (G.layerCoords 1).card = G.delta := by
      rw [h.layer1, List.toFinset_card_of_nodup h.nodup]; exact h.deg
    show (G.layerCoords 1).card = G.delta - 0
    omega
  | succ k => exact h.card_formula k

theorem interior_card_le_layer
     (hw : G.BFSWF) (hirr : G.IsIrreflexive)
    (u v v0 : \alpha) (k : Nat) (hL : LayerShrink G v0)
    (hu_node : u ∈ G.nodes) (hv_node : v ∈ G.nodes)
    (hd : v.dist = u.dist + 1) (hk : v.dist = k + 1)
    (hnb : G.backNeighbors u v = ∅) :
    (G.interiorNeighbors u v).card ≤ G.delta - k - 1 := by
  have hsub := interior_subset_layer G hw u v hu_node hv_node hd hnb
  have hv_in : v.toCoords ∈ G.layerCoords v.dist :=
    mem_layerCoords_of_node G v _ hv_node rfl
  have hsub' : G.interiorNeighbors u v ⊆ (G.layerCoords v.dist).erase v.toCoords := by
    intro c hc
    rw [Finset.mem_erase]
    refine ⟨?_, hsub hc⟩
    intro hcv
    have h2 := (interior_neighbors_implies_first_neighbors G u v c
      (cond_of_nodes hu_node hv_node hd) hc).2
    exact hirr v hv_node (by rw [← hcv]; exact h2)
  have hcard := Finset.card_le_card hsub'
  rw [Finset.card_erase_of_mem hv_in, hk, hL.card_succ k] at hcard
  omega

theorem oriented_arcs_le {α : Type*} [DecidableEq α] (R : Finset α)
    (A : Finset (α × α)) (hA : A ⊆ R.offDiag)
    (hanti : ∀ p ∈ A, (p.2, p.1) ∉ A) :
    2 * A.card ≤ R.card * R.card - R.card := by
  have hsw : (A.image Prod.swap) ⊆ R.offDiag := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := Finset.mem_offDiag.mp (hA hq)
    exact Finset.mem_offDiag.mpr ⟨this.2.1, this.1, fun h => this.2.2 h.symm⟩
  have hdis : Disjoint A (A.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hpA hpI
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hpI
    exact hanti q hq hpA
  have hcard : (A.image Prod.swap).card = A.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have := Finset.card_le_card (Finset.union_subset hA hsw)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.offDiag_card] at this
  omega

theorem no_layer_past_third (δ : Nat) (hδ : 1 ≤ δ)
    (hlayer : ∀ i, 1 ≤ i → i ≤ δ → 3 * i ≤ δ) : False := by
  have := hlayer (δ / 3 + 1) (by omega) (by omega)
  omega

theorem last_layer_le (δ i : Nat) (h : 3 * i ≤ δ) : i ≤ δ / 3 := by omega

theorem first_forbidden (δ : Nat) : ¬ (3 * (δ / 3 + 1) ≤ δ) := by omega

theorem feasibility (n i δ : Nat) (hn : n = δ - i + 1) (hi : i ≤ δ)
    (h : 2 * (n * i) ≤ n * n - n) : 3 * i ≤ δ := by
  have hpos : 0 < n := by omega
  have h2 : n * (2 * i) ≤ n * (n - 1) := by
    have e1 : n * (2 * i) = 2 * (n * i) := Nat.mul_left_comm n 2 i
    have e2 : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
    rw [e1, e2]
    exact h
  have h3 : 2 * i ≤ n - 1 := Nat.le_of_mul_le_mul_left h2 hpos
  omega

/-- Layers collapse at depth ⌊δ/3⌋: the size formula and the interior-arc
    capacity bound cannot both hold at layer ⌊δ/3⌋ + 1. -/
theorem layers_collapse (δ : Nat) (hδ : 1 ≤ δ) (s : Nat → Nat)
    (hsize : ∀ i, 1 ≤ i → i ≤ δ → s i = δ - i + 1)
    (hcap  : ∀ i, 1 ≤ i → i ≤ δ → 2 * (s i * i) ≤ s i * s i - s i) :
    False := by
  have hi1 : 1 ≤ δ / 3 + 1 := by omega
  have hi2 : δ / 3 + 1 ≤ δ := by omega
  have h3 := feasibility (s (δ / 3 + 1)) (δ / 3 + 1) δ
    (hsize _ hi1 hi2) hi2 (hcap _ hi1 hi2)
  omega

theorem layers_collapse_G  (hδ : 1 ≤ G.delta)
    (hsize : ∀ i, 1 ≤ i → i ≤ G.delta →
      (G.layerCoords i).card = G.delta - i + 1)
    (hcap : ∀ i, 1 ≤ i → i ≤ G.delta →
      2 * ((G.layerCoords i).card * i)
        ≤ (G.layerCoords i).card * (G.layerCoords i).card - (G.layerCoords i).card) :
    False :=
  layers_collapse G.delta hδ (fun i => (G.layerCoords i).card) hsize hcap

theorem layer_size_all
     (delta : Nat) (v0 : \alpha)
    (h_v0_deg : v0.out_neighbors.length = delta)
    (h_v0_nodup : v0.out_neighbors.Nodup)
    (h_layer1_eq : (G.layerCoords 1).card = v0.out_neighbors.toFinset.card)
    (h_step : ∀ j, 1 ≤ j →
      (G.layerCoords (j + 1)).card = (G.layerCoords j).card - 1) :
    ∀ i, 1 ≤ i → i ≤ delta → (G.layerCoords i).card = delta - i + 1 := by
  intro i hi hid
  have h1 : (G.layerCoords 1).card = delta := by
    rw [h_layer1_eq, List.toFinset_card_of_nodup h_v0_nodup]
    exact h_v0_deg
  rcases Nat.lt_or_ge i 2 with h | h
  · obtain rfl : i = 1 := by omega
    rw [h1]; omega
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    rw [layer_size_formula G delta v0 h_v0_deg h_v0_nodup h_layer1_eq h_step m]
    omega

/-- hsize: from `layer_size_all`, with `h_step` from the no-back-arc invariant. -/
theorem layer_size_of_min
    (hG : IsMinimumCounterexample G)
    (hbfs : G.BFSWF)
    (hroot : ∃ r ∈ G.nodes, r.dist = 0 ∧ r.out_neighbors.length = G.delta) :
    ∀ i, 1 ≤ i → i ≤ G.delta →
      (G.layerCoords i).card = G.delta - i + 1 := by
  obtain ⟨hce, _hmin⟩ := hG
  obtain ⟨hcu, hor, hne, hall⟩ := hce
  obtain ⟨v0, hv0, hv0d, hdeg⟩ := hroot
  exact layer_size_formula G G.delta v0 hdeg
    (root_nodup G v0 hv0)
    (layer1_eq_root_out G v0 hv0 hv0d)
    (layer_step G hbfs hcu hor hall)

/-- hcap: from `layer_arc_count`, using interior degree i in every node of R_i. -/
theorem layer_cap_of_min
    (hG : IsMinimumCounterexample G) :
    ∀ i, 1 ≤ i → i ≤ G.delta →
      2 * ((G.layerCoords i).card * i)
        ≤ (G.layerCoords i).card * (G.layerCoords i).card - (G.layerCoords i).card := by
  sorry  -- layer_arc_count

theorem no_minimum_layered_counterexample
     (hG : IsMinimumCounterexample G)
    (h3 : 3 ≤ G.delta) : False :=
  layers_collapse_G G (by omega) (layer_size_of_min G hG) (layer_cap_of_min G hG)

-/
