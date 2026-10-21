import OpenProblem.WOWII256

/-!
# Written on the Wall II, Conjecture 255 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 255.** If `G` is a simple connected graph, then
> `γ_t(G) ≥ 2|C| / max {|N(e)| : e an edge of G}`, where `C` is the set of vertices that are
> centers of `G`.

Here `γ_t` is the total domination number and `N(e) = N(u) ∪ N(v)` for an edge `e = uv`.

The conjecture fails for the following graph on 11 vertices with 20 edges (`not_conjecture255`).

* A vertex `c = 0` is adjacent to `ℓ₁ = 1` and `ℓ₂ = 2`.
* `ℓ₁` is adjacent to the independent vertices `3, 4, 5, 6`. `ℓ₂` is adjacent to `7, 8, 9, 10`,
  which form a clique.
* The matching `3-7`, `4-8`, `5-9`, `6-10` joins the two groups.

Any two vertices are adjacent or have a common neighbour, and no vertex is adjacent to all others,
so every vertex has eccentricity 2 and `C = V`. The largest `|N(e)|` is 7, but `{c, ℓ₁, ℓ₂}` is a
total dominating set, so `γ_t ≤ 3 < 22/7`. An exhaustive search finds no counterexample on at most
10 vertices, so this one has the least possible order.

The same works with any graph `H` on the first group and its complement on the second; with `p`
vertices in each group the bound is `2(2p + 3)/(p + 3) > 3` for every `p ≥ 4`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII255

open WOWII372 WOWII256

variable {V : Type*} [Fintype V]

/-- The eccentricity of `v`. -/
def ecc (G : SimpleGraph V) (v : V) : ℕ := univ.sup fun w => G.dist v w

/-- The center: the vertices of minimum eccentricity. -/
def center (G : SimpleGraph V) : Finset V := univ.filter fun v => ∀ w, ecc G v ≤ ecc G w

/-- The statement of Conjecture 255. -/
def Conjecture255 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    (2 * #(center G) : ℚ) / maxEdgeNbhd G ≤ totalDomNum G

/-! ### The counterexample -/

/-- The edges of the counterexample. -/
def E : List (Fin 11 × Fin 11) :=
  [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 7),
    (4, 8), (5, 9), (6, 10), (7, 8), (7, 9), (7, 10), (8, 9), (8, 10), (9, 10)]

/-- Adjacency in the counterexample. -/
def adjB (a b : Fin 11) : Bool := E.contains (a, b) || E.contains (b, a)

/-- The counterexample. -/
def G : SimpleGraph (Fin 11) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 11} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 11, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

/-- Any two vertices are at distance at most two. -/
lemma G_dist_le (v w : Fin 11) : G.Reachable v w ∧ G.dist v w ≤ 2 := by
  by_cases hvw : v = w
  · subst hvw; simp
  by_cases h1 : adjB v w = true
  · have h := G_adj.mpr h1
    exact ⟨h.reachable, by rw [dist_eq_one_iff_adj.mpr h]; omega⟩
  · have : ∃ u, adjB v u = true ∧ adjB u w = true := by revert v w; decide
    obtain ⟨u, hu, huw⟩ := this
    let p : G.Walk v w := Walk.cons (G_adj.mpr hu) (Walk.cons (G_adj.mpr huw) Walk.nil)
    exact ⟨p.reachable, (dist_le p).trans (le_of_eq rfl)⟩

lemma G_connected : G.Connected :=
  (connected_iff_exists_forall_reachable G).mpr ⟨0, fun w => (G_dist_le 0 w).1⟩

/-- Every vertex has eccentricity two. -/
lemma G_ecc (v : Fin 11) : ecc G v = 2 := by
  apply le_antisymm
  · exact Finset.sup_le fun w _ => (G_dist_le v w).2
  · have : ∃ w, w ≠ v ∧ adjB v w = false := by revert v; decide
    obtain ⟨w, hwv, hvw⟩ := this
    have h := G_connected.one_lt_dist_of_ne_of_not_adj (Ne.symm hwv)
      (by rw [G_adj, hvw]; decide)
    exact h.trans_le (le_sup (f := fun w => G.dist v w) (mem_univ w))

lemma G_center : #(center G) = 11 := by
  have : center G = univ := by
    ext v
    simp [center, G_ecc]
  rw [this, card_univ, Fintype.card_fin]

lemma G_maxEdgeNbhd_le : maxEdgeNbhd G ≤ 7 := by
  refine Finset.sup_le fun e he => ?_
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgeSet, G_adj] at he
    have key : ∀ u v : Fin 11, adjB u v = true →
        #(univ.filter fun x => adjB u x = true ∨ adjB v x = true) ≤ 7 := by decide
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
  refine Nat.sInf_le ⟨{0, 1, 2}, fun v => ?_, rfl⟩
  have : ∃ u ∈ ({0, 1, 2} : Finset (Fin 11)), adjB v u = true := by revert v; decide
  obtain ⟨u, hu, hvu⟩ := this
  exact ⟨u, hu, G_adj.mpr hvu⟩

/-- **WOWII Conjecture 255 is false.** -/
theorem not_conjecture255 : ¬ Conjecture255 := by
  intro h
  have h1 := h (Fin 11) G G_connected
  rw [G_center] at h1
  have h2 : (totalDomNum G : ℚ) ≤ 3 := by exact_mod_cast G_totalDomNum
  have h3 : (maxEdgeNbhd G : ℚ) ≤ 7 := by exact_mod_cast G_maxEdgeNbhd_le
  have h4 : (0 : ℚ) < maxEdgeNbhd G := by exact_mod_cast G_maxEdgeNbhd_pos
  rw [div_le_iff₀ h4] at h1
  push_cast at h1
  nlinarith

end WOWII255
