import OpenProblem.WOWII372

/-!
# Written on the Wall II, Conjecture 256 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 256.** If `G` is a simple connected graph, then
> `γ_t(G) ≥ 2|N(A)| / max {|N(e)| : e an edge of G}`, where `A` is the set of vertices of minimum
> degree.

Here `γ_t` is the total domination number, `N(A)` the set of neighbours of vertices of `A`, and
`N(e) = N(u) ∪ N(v)` for an edge `e = uv`.

The conjecture fails for the following graph on 15 vertices with 20 edges (`not_conjecture256`).

* A vertex `c = 0` is adjacent to two vertices `ℓ₁ = 1` and `ℓ₂ = 8`.
* Each `ℓᵢ` has six further neighbours, matched in pairs by three edges: `2-3`, `4-5`, `6-7` at
  `ℓ₁` and `9-10`, `11-12`, `13-14` at `ℓ₂`.

Every vertex other than `ℓ₁` and `ℓ₂` has degree 2, so `N(A)` is everything except `c`, which gives
`|N(A)| = 14`. The largest `|N(e)|` is 9, on the edges `cℓᵢ`. But `{c, ℓ₁, ℓ₂}` is a total
dominating set, so `γ_t = 3 < 28/9`.

The same bound fails, with `γ_t = t + 1`, for `t ≥ 2` such vertices `ℓᵢ` with `p ≥ 6` private
neighbours each when `(t + 1)(t + p + 1) < 2t(p + 1)`. An exhaustive search finds no
counterexample on at most 10 vertices.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII256

open WOWII372

variable {V : Type*} [Fintype V]

/-- The vertices of minimum degree. -/
def minDegSet (G : SimpleGraph V) : Finset V := univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

/-- The neighbourhood `N(S)` of a set of vertices. -/
def nbhd (G : SimpleGraph V) (S : Finset V) : Finset V := univ.filter fun x => ∃ a ∈ S, G.Adj a x

/-- `|N(e)| = |N(u) ∪ N(v)|` for an edge `e = uv`. -/
def edgeNbhdCard (G : SimpleGraph V) (e : Sym2 V) : ℕ := #(univ.filter fun x => ∃ u ∈ e, G.Adj u x)

/-- The largest `|N(e)|` over the edges of `G`. -/
def maxEdgeNbhd (G : SimpleGraph V) : ℕ := G.edgeFinset.sup (edgeNbhdCard G)

/-- The statement of Conjecture 256. -/
def Conjecture256 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    (2 * #(nbhd G (minDegSet G)) : ℚ) / maxEdgeNbhd G ≤ totalDomNum G

/-! ### The counterexample -/

/-- The edges of the counterexample. -/
def E : List (Fin 15 × Fin 15) :=
  [(0, 1), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (4, 5), (6, 7),
    (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 10), (11, 12), (13, 14)]

/-- Adjacency in the counterexample. -/
def adjB (a b : Fin 15) : Bool := E.contains (a, b) || E.contains (b, a)

/-- The counterexample. -/
def G : SimpleGraph (Fin 15) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 15} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 15, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 15) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw]
  by_cases h1 : adjB 0 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 0 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

lemma G_minDegSet : minDegSet G = univ.filter fun v => v ≠ 1 ∧ v ≠ 8 := by
  ext v
  simp only [minDegSet, mem_filter, mem_univ, true_and, G_degree]
  revert v
  decide

lemma G_nbhd : #(nbhd G (minDegSet G)) = 14 := by
  rw [G_minDegSet]
  simp only [nbhd, G_adj]
  decide

lemma G_maxEdgeNbhd_le : maxEdgeNbhd G ≤ 9 := by
  refine Finset.sup_le fun e he => ?_
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgeSet, G_adj] at he
    have key : ∀ u v : Fin 15, adjB u v = true →
        #(univ.filter fun x => adjB u x = true ∨ adjB v x = true) ≤ 9 := by decide
    have := key u v he
    simpa only [edgeNbhdCard, Sym2.mem_iff, exists_eq_or_imp, exists_eq_left, G_adj] using this

lemma G_maxEdgeNbhd_pos : 0 < maxEdgeNbhd G := by
  have he : s(0, 1) ∈ G.edgeFinset := by
    rw [mem_edgeFinset, mem_edgeSet, G_adj]
    decide
  refine lt_of_lt_of_le ?_ (le_sup (f := edgeNbhdCard G) he)
  refine card_pos.mpr ⟨1, ?_⟩
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨0, Sym2.mem_mk_left 0 1, G_adj.mpr (by decide)⟩

lemma G_totalDomNum : totalDomNum G ≤ 3 := by
  refine Nat.sInf_le ⟨{0, 1, 8}, fun v => ?_, rfl⟩
  have : ∃ u ∈ ({0, 1, 8} : Finset (Fin 15)), adjB v u = true := by revert v; decide
  obtain ⟨u, hu, hvu⟩ := this
  exact ⟨u, hu, G_adj.mpr hvu⟩

/-- **WOWII Conjecture 256 is false.** -/
theorem not_conjecture256 : ¬ Conjecture256 := by
  intro h
  have h1 := h (Fin 15) G G_connected
  rw [G_nbhd] at h1
  have h2 : (totalDomNum G : ℚ) ≤ 3 := by exact_mod_cast G_totalDomNum
  have h3 : (maxEdgeNbhd G : ℚ) ≤ 9 := by exact_mod_cast G_maxEdgeNbhd_le
  have h4 : (0 : ℚ) < maxEdgeNbhd G := by exact_mod_cast G_maxEdgeNbhd_pos
  rw [div_le_iff₀ h4] at h1
  push_cast at h1
  nlinarith

end WOWII256
