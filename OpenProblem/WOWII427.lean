import OpenProblem.WOWII255
import OpenProblem.WOWII319
import OpenProblem.WOWII391
import OpenProblem.WOWII422b

/-!
# Written on the Wall II, Conjecture 427 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 427.** Let `G` be a connected graph on `n > 3` vertices and `M` the vertices of
> maximum degree. Then `i(G) ≤ |E(C, V - C)| + ⌊(2/3) |E(G[V - N(P)])|⌋`.

Here `i` is the independent domination number, `E(C, V - C)` the set of edges with exactly one
end in `C`, and `P` the set of pendant vertices, as elsewhere in the list. The statement never
defines `C`. Its first sentence is the preamble of the neighbouring Conjecture 422b, which suggests
`C = M`. Elsewhere in the list `C` is the centre of `G`. We refute both readings with one tree
(`not_conjecture427` for the centre and `not_conjecture427M` for `M`).

The tree has 11 vertices and graph6 code `JqOI?C_G??_`. The centre `0` is adjacent to `1` and `7`.
The vertex `1` is adjacent to the leaf `2` and starts the paths `1 - 3 - 4` and `1 - 5 - 6`. The
vertex `7` is adjacent to the leaf `8` and starts the path `7 - 9 - 10`.

* The leaves are `2, 4, 6, 8, 10`, and their neighbours are `1, 3, 5, 7, 9`. So
  `V - N(P) = {0, 2, 4, 6, 8, 10}` spans no edge, and the floor term is `0`.
* The centre is `{0}`, which meets `2` edges. The only vertex of maximum degree `4` is `1`, which
  meets `4` edges. So the bound is `2` under the first reading and `4` under the second.
* Every dominating set contains `2k - 1` or `2k` for each `k = 1, ..., 5`, so `i(G) ≥ 5`.

The search behind this tree found that the centre reading already fails on 8 vertices (for
example `G?`DB_`) and that the reading `C = M` holds for all connected graphs with at most 9
vertices.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII427

open WOWII179 WOWII422b WOWII449

variable {V : Type*} [Fintype V]

/-- The number of edges with exactly one end in `A`. -/
def edgeCut (G : SimpleGraph V) (A : Finset V) : ℕ :=
  #(G.edgeFinset.filter fun e => (∃ u ∈ e, u ∈ A) ∧ ∃ v ∈ e, v ∉ A)

/-- The vertices outside `N(P)`, where `P` is the set of pendant vertices. -/
def outsideSupport (G : SimpleGraph V) : Finset V :=
  univ \ WOWII412f.nbhd G (WOWII412f.pendants G)

/-- The statement of Conjecture 427, with `C` the centre of `G`. -/
def Conjecture427 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    indepDomNum G ≤ edgeCut G (WOWII255.center G) + 2 * edgesIn G (outsideSupport G) / 3

/-- The statement of Conjecture 427, with `C = M` the vertices of maximum degree. -/
def Conjecture427M : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    indepDomNum G ≤ edgeCut G (maxDegSet G) + 2 * edgesIn G (outsideSupport G) / 3

/-- The edges leaving a single vertex all meet it. -/
lemma edgeCut_singleton_le (H : SimpleGraph V) (a : V) : edgeCut H {a} ≤ H.degree a := by
  rw [← card_incidenceFinset_eq_degree]
  refine card_le_card fun e he => ?_
  rw [mem_filter] at he
  obtain ⟨he, ⟨u, hu, hua⟩, -⟩ := he
  rw [mem_singleton] at hua
  subst hua
  rw [mem_incidenceFinset]
  exact ⟨mem_edgeFinset.mp he, hu⟩

/-! ### The counterexample -/

/-- The edges of the tree. -/
def E : List (Fin 11 × Fin 11) :=
  [(0, 1), (0, 7), (1, 2), (1, 3), (3, 4), (1, 5), (5, 6), (7, 8), (7, 9), (9, 10)]

/-- Adjacency in the tree. -/
def adjB (a b : Fin 11) : Bool := E.contains (a, b) || E.contains (b, a)

/-- The tree, with graph6 code `JqOI?C_G??_`. -/
def G : SimpleGraph (Fin 11) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 11} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 11, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 11) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

/-- The distances in the tree. -/
def D : Fin 11 → Fin 11 → ℕ :=
  ![![0, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3],
    ![1, 0, 1, 1, 2, 1, 2, 2, 3, 3, 4],
    ![2, 1, 0, 2, 3, 2, 3, 3, 4, 4, 5],
    ![2, 1, 2, 0, 1, 2, 3, 3, 4, 4, 5],
    ![3, 2, 3, 1, 0, 3, 4, 4, 5, 5, 6],
    ![2, 1, 2, 2, 3, 0, 1, 3, 4, 4, 5],
    ![3, 2, 3, 3, 4, 1, 0, 4, 5, 5, 6],
    ![1, 2, 3, 3, 4, 3, 4, 0, 1, 1, 2],
    ![2, 3, 4, 4, 5, 4, 5, 1, 0, 2, 3],
    ![2, 3, 4, 4, 5, 4, 5, 1, 2, 0, 1],
    ![3, 4, 5, 5, 6, 5, 6, 2, 3, 1, 0]]

lemma G_dist (v u : Fin 11) : G.Reachable v u ∧ G.dist v u = D v u := by
  refine WOWII319.dist_eq_of_bfs G v (D v) ?_ ?_ ?_ ?_ u
  · revert v; decide
  · revert v; decide
  · intro x y hxy
    rw [G_adj] at hxy
    revert v x y; decide
  · intro u hu
    have : ∃ w, adjB w u = true ∧ D v w + 1 = D v u := by revert v u; decide
    obtain ⟨w, hw, hwu⟩ := this
    exact ⟨w, G_adj.mpr hw, hwu⟩

lemma G_connected : G.Connected :=
  (connected_iff_exists_forall_reachable G).mpr ⟨0, fun u => (G_dist 0 u).1⟩

lemma G_center : WOWII255.center G = {0} := by
  ext v
  simp only [WOWII255.center, WOWII255.ecc, fun v w => (G_dist v w).2, mem_filter, mem_univ, true_and,
    mem_singleton]
  revert v
  decide

lemma G_maxDegree : G.maxDegree = 4 := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rw [G_degree]
    revert v
    decide
  · have : G.degree 1 = 4 := by rw [G_degree]; decide
    rw [← this]
    exact G.degree_le_maxDegree 1

lemma G_maxDegSet : maxDegSet G = {1} := by
  ext v
  simp only [maxDegSet, mem_filter, mem_univ, true_and, G_maxDegree, G_degree, mem_singleton]
  revert v
  decide

lemma G_pendants : WOWII412f.pendants G = {2, 4, 6, 8, 10} := by
  ext v
  simp only [WOWII412f.pendants, mem_filter, mem_univ, true_and, G_degree, mem_insert,
    mem_singleton]
  revert v
  decide

lemma G_outsideSupport : outsideSupport G = {0, 2, 4, 6, 8, 10} := by
  ext v
  simp only [outsideSupport, WOWII412f.nbhd, G_pendants, mem_sdiff, mem_univ, true_and,
    mem_filter, G_adj, mem_insert, mem_singleton]
  revert v
  decide

/-- A vertex set spanning no edge has `edgesIn = 0`. -/
lemma edgesIn_eq_zero (H : SimpleGraph V) (A : Finset V) (hA : ∀ u ∈ A, ∀ v ∈ A, ¬ H.Adj u v) :
    edgesIn H A = 0 := by
  rw [edgesIn, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_filter] at he
  induction e using Sym2.ind with
  | _ u v =>
    have := he.1
    rw [mem_edgeFinset, mem_edgeSet] at this
    exact hA u (he.2 u (Sym2.mem_mk_left u v)) v (he.2 v (Sym2.mem_mk_right u v)) this

lemma G_edgesIn : edgesIn G (outsideSupport G) = 0 := by
  refine edgesIn_eq_zero G _ fun u hu v hv huv => ?_
  rw [G_outsideSupport] at hu hv
  rw [G_adj] at huv
  -- every edge has an odd end, and the vertices outside `N(P)` are even
  have key : ∀ u v : Fin 11, adjB u v = true → u.val % 2 = 1 ∨ v.val % 2 = 1 := by decide
  have even : ∀ x ∈ ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)), x.val % 2 = 0 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have := even u hu
  have := even v hv
  rcases key u v huv with h | h <;> omega

/-- Every dominating set of the tree has at least five vertices. -/
lemma card_ge {S : Finset (Fin 11)} (hS : IsDom G S) : 5 ≤ #S := by
  -- each leaf `2k` is dominated by itself or by its neighbour `2k - 1`
  have key : ∀ u w : Fin 11, w.val % 2 = 0 → 0 < w.val → adjB w u = true → u.val + 1 = w.val := by
    decide
  have hsub : Icc 1 5 ⊆ S.image fun v : Fin 11 => ((v : ℕ) + 1) / 2 := by
    intro k hk
    rw [mem_Icc] at hk
    rw [mem_image]
    rcases hS ⟨2 * k, by omega⟩ with h | ⟨u, hu, h⟩
    · exact ⟨_, h, by simp only; omega⟩
    · have := key u ⟨2 * k, by omega⟩ (by simp) (by simp only; omega) (G_adj.mp h)
      exact ⟨u, hu, by simp only at this; omega⟩
  have := (card_le_card hsub).trans card_image_le
  simpa using this

lemma G_indepDomNum : 5 ≤ indepDomNum G := by
  refine le_csInf ⟨5, {1, 4, 6, 7, 10}, ?_, ?_, rfl⟩ ?_
  · have : ∀ v : Fin 11, v ∈ ({1, 4, 6, 7, 10} : Finset (Fin 11)) ∨
        ∃ u ∈ ({1, 4, 6, 7, 10} : Finset (Fin 11)), adjB v u = true := by decide
    simpa only [IsDom, G_adj] using this
  · intro x hx y hy hxy
    have : ∀ x ∈ ({1, 4, 6, 7, 10} : Finset (Fin 11)),
        ∀ y ∈ ({1, 4, 6, 7, 10} : Finset (Fin 11)), adjB x y = false := by decide
    rw [G_adj, this x hx y hy] at hxy
    exact absurd hxy (by decide)
  · rintro k ⟨S, hS, -, rfl⟩
    exact card_ge hS

/-- **WOWII Conjecture 427 is false** when `C` is the centre. -/
theorem not_conjecture427 : ¬ Conjecture427 := by
  intro h
  have h1 := h (Fin 11) G G_connected (by simp)
  rw [G_center, G_edgesIn] at h1
  have := edgeCut_singleton_le G 0
  have h0 : G.degree 0 = 2 := by rw [G_degree]; decide
  have := G_indepDomNum
  omega

/-- **WOWII Conjecture 427 is false** when `C = M` is the set of vertices of maximum degree. -/
theorem not_conjecture427M : ¬ Conjecture427M := by
  intro h
  have h1 := h (Fin 11) G G_connected (by simp)
  rw [G_maxDegSet, G_edgesIn] at h1
  have := edgeCut_singleton_le G 1
  have h0 : G.degree 1 = 4 := by rw [G_degree]; decide
  have := G_indepDomNum
  omega

end WOWII427
