import OpenProblem.WOWII449
import OpenProblem.WOWII426

/-!
# Written on the Wall II, Conjecture 439 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 439.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ |N(M)| + ⌊2(CW(G) - 1)⌋`, where `M` is the set of maximum degree vertices and `CW(G)`
> is the Caro–Wei invariant of `G`.

Here `α_2` is the 2-independence number, the largest size of a set inducing a subgraph of maximum
degree at most one, and `CW(G) = ∑_v 1 / (deg v + 1)`.

The counterexample `G` has 15 vertices and 26 edges and was found by simulated annealing.

* Vertices `0, …, 9` induce the perfect matching `01, 23, 45, 67, 89`, so `α_2(G) ≥ 10`.
* Vertex `14` is the only vertex of maximum degree `5`, so `|N(M)| = 5`.
* The degrees give `CW(G) = 69/20`, so `⌊2(CW(G) - 1)⌋ = ⌊49/10⌋ = 4`.

So the bound is `9 < 10`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII439

open WOWII449 WOWII422b WOWII426

variable {V : Type*} [Fintype V]

/-- The Caro–Wei invariant `∑_v 1 / (deg v + 1)`. -/
def caroWei (G : SimpleGraph V) : ℚ := ∑ v, 1 / ((G.degree v : ℚ) + 1)

/-- The statement of Conjecture 439. -/
def Conjecture439 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    (twoIndepNum G : ℤ) ≤ #(nbhd G (maxDegSet G)) + ⌊2 * (caroWei G - 1)⌋

/-! ### The counterexample -/

def E : List (Fin 15 × Fin 15) :=
  [(0, 1), (0, 10), (0, 12), (0, 14), (1, 11), (1, 12), (1, 14), (2, 3), (2, 11), (2, 13),
    (3, 10), (3, 14), (4, 5), (4, 13), (5, 10), (5, 14), (6, 7), (6, 12), (6, 14), (7, 10),
    (7, 11), (8, 9), (8, 11), (8, 13), (9, 12), (9, 13)]

def adjB (a b : Fin 15) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 15) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 15} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 15, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨14, fun w => ?_⟩
  have key : ∀ w : Fin 15, w = 14 ∨ adjB 14 w = true ∨ (∃ u, adjB 14 u = true ∧ adjB u w = true) ∨
      ∃ u x, adjB 14 u = true ∧ adjB u x = true ∧ adjB x w = true := by decide
  rcases key w with h | h | ⟨u, hu, huw⟩ | ⟨u, x, hu, hux, hxw⟩
  · rw [h]
  · exact (G_adj.mpr h).reachable
  · exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable
  · exact ((G_adj.mpr hu).reachable.trans (G_adj.mpr hux).reachable).trans
      (G_adj.mpr hxw).reachable

/-- The degrees of `G`. -/
def degL : Fin 15 → ℕ := ![4, 4, 3, 3, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5]

lemma G_degree (v : Fin 15) : G.degree v = degL v := by
  rw [← card_neighborFinset_eq_degree]
  have : G.neighborFinset v = univ.filter fun w => adjB v w = true := by
    ext w
    simp [G_adj]
  rw [this]
  clear this
  revert v
  decide

lemma G_maxDegree : G.maxDegree = 5 := by
  refine le_antisymm (G.maxDegree_le_of_forall_degree_le 5 fun v => ?_) ?_
  · rw [G_degree]
    revert v
    decide
  · have := G.degree_le_maxDegree 14
    rwa [G_degree] at this

lemma G_maxDegSet : maxDegSet G = {14} := by
  ext v
  simp only [maxDegSet, mem_filter, mem_univ, true_and, G_degree, G_maxDegree, mem_singleton]
  revert v
  decide

lemma G_nbhd : #(nbhd G {14}) = 5 := by
  have : nbhd G {14} = univ.filter fun v => adjB v 14 = true := by
    ext v
    simp [nbhd, G_adj]
  rw [this]
  decide

lemma G_caroWei : caroWei G = 69 / 20 := by
  simp only [caroWei, G_degree, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [degL]

/-- `{0, …, 9}` induces a perfect matching, so `α_2(G) ≥ 10`. -/
lemma G_twoIndepNum : 10 ≤ twoIndepNum G := by
  let S : Finset (Fin 15) := univ.filter fun v => v.val < 10
  have hS : IsTwoIndep G S := by
    intro v hv
    have : S.filter (G.Adj v) = S.filter fun w => adjB v w = true := by
      ext w
      simp only [mem_filter, G_adj]
    rw [this]
    clear this
    revert v
    decide
  exact le_csSup (bddAbove_twoIndep G) ⟨S, hS, by decide⟩

/-- **WOWII Conjecture 439 is false.** -/
theorem not_conjecture439 : ¬ Conjecture439 := by
  intro h
  have h1 := h (Fin 15) G G_connected (by simp)
  rw [G_maxDegSet, G_nbhd, G_caroWei] at h1
  have h2 : ⌊(2 : ℚ) * (69 / 20 - 1)⌋ = 4 := by norm_num [Int.floor_eq_iff]
  rw [h2] at h1
  have := G_twoIndepNum
  omega

end WOWII439
