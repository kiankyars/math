import OpenProblem.WOWII382b
import OpenProblem.WOWII402
import OpenProblem.WOWII449
import OpenProblem.WOWII422b

/-!
# Written on the Wall II, Conjecture 399b is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 399b.** If `G` is a connected graph on `n > 2` vertices, then
> `γ_2 ≤ WP(Ḡ) + ⌊3 / α(G[A_3])⌋`, where `A_3` is the set of vertices of degree at least three.

Here `γ_2` is the 2-domination number, `α` the independence number and `WP` the Welsh–Powell
number: `WP(H) = max_i min(d_i + 1, i)` for the degrees `d_1 ≥ d_2 ≥ ⋯` of `H`. Equivalently,
`WP(H)` is the largest `k` such that at least `k` vertices of `H` have degree at least `k - 1`.
This is the form we use.

The counterexample `G` has 12 vertices and was found by simulated annealing. Vertices `4, …, 11`
form a `K_8`, and the independent vertices `0, 1, 2, 3` are attached by

  `N(0) = {4, 10}`, `N(1) = {5, 8, 11}`, `N(2) = {9, 10, 11}`, `N(3) = {6, 7, 11}`.

* Only `0, 1, 2, 3` have at least four non-neighbours, so `WP(Ḡ) = 4`.
* `{1, 2, 3, 4}` is an independent set of vertices of degree at least three, so
  `⌊3 / α(G[A_3])⌋ = 0`.
* No four vertices 2-dominate `G`. A vertex of `0, 1, 2, 3` outside the set needs two neighbours
  inside, and no two of `N(0), …, N(3)` share two vertices. So `γ_2(G) = 5`.

So the bound is `4 < 5`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII399b

open WOWII382b WOWII402 WOWII422b WOWII449

variable {V : Type*} [Fintype V]

/-- The Welsh–Powell number: the largest `k` such that at least `k` vertices have degree at least
`k - 1`. This equals `max_i min(d_i + 1, i)` for the degrees in nonincreasing order. -/
def WP (H : SimpleGraph V) : ℕ := sSup {k | k ≤ #(univ.filter fun v => k ≤ H.degree v + 1)}

/-- The independence number of `G[A]`. -/
def alphaIn (G : SimpleGraph V) (A : Finset V) : ℕ := sSup {k | ∃ S ⊆ A, IsIndep G S ∧ #S = k}

lemma degree_eq_card_filter (H : SimpleGraph V) (v : V) : H.degree v = #(univ.filter (H.Adj v)) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext
  simp

/-- The statement of Conjecture 399b. -/
def Conjecture399b : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ WP Gᶜ + 3 / alphaIn G (H3 G)

/-! ### The counterexample -/

def E : List (Fin 12 × Fin 12) :=
  [(0, 4), (0, 10), (1, 5), (1, 8), (1, 11), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 11),
    (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9),
    (5, 10), (5, 11), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 8), (7, 9), (7, 10),
    (7, 11), (8, 9), (8, 10), (8, 11), (9, 10), (9, 11), (10, 11)]

def adjB (a b : Fin 12) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 12} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨11, fun w => ?_⟩
  by_cases hw : w = 11
  · rw [hw]
  by_cases h1 : adjB 11 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 11 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

/-- The degrees of `G`. -/
def degL : Fin 12 → ℕ := ![2, 3, 3, 3, 8, 8, 8, 8, 8, 8, 9, 10]

lemma G_degree (v : Fin 12) : G.degree v = degL v := by
  rw [← card_neighborFinset_eq_degree]
  have : G.neighborFinset v = univ.filter fun w => adjB v w = true := by
    ext w
    simp [G_adj]
  rw [this]
  clear this
  revert v
  decide

/-- Only `0, 1, 2, 3` have at least four non-neighbours, so `WP(Ḡ) ≤ 4`. -/
lemma G_WP : WP Gᶜ ≤ 4 := by
  refine csSup_le ⟨0, by simp⟩ fun k hk => ?_
  have hk' := hk
  simp only [Set.mem_ofPred_eq] at hk'
  by_contra hlt
  push Not at hlt
  have h4 : #(univ.filter fun v : Fin 12 => v.val < 4) = 4 := by decide
  have key : ∀ v : Fin 12,
      4 ≤ #(univ.filter fun w => w ≠ v ∧ adjB v w = false) → v.val < 4 := by decide
  have := hk'.trans (card_le_card (t := univ.filter fun v : Fin 12 => v.val < 4) fun v hv => by
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    rw [degree_eq_card_filter] at hv
    apply key v
    have h' : k ≤ #(univ.filter fun w => w ≠ v ∧ adjB v w = false) + 1 := by
      refine hv.trans (Nat.add_le_add_right (card_le_card fun w hw => ?_) 1)
      simp only [mem_filter, mem_univ, true_and, compl_adj, G_adj, Bool.not_eq_true] at hw ⊢
      exact ⟨hw.1.symm, hw.2⟩
    omega)
  omega

/-- `{1, 2, 3, 4}` is an independent set of vertices of degree at least three. -/
lemma G_alphaIn : 4 ≤ alphaIn G (H3 G) := by
  have hbdd : BddAbove {k | ∃ S ⊆ H3 G, IsIndep G S ∧ #S = k} :=
    ⟨Fintype.card (Fin 12), fun _ ⟨S, _, _, hk⟩ => hk ▸ card_le_univ S⟩
  refine le_csSup hbdd ⟨{1, 2, 3, 4}, ?_, ?_, by decide⟩
  · intro v hv
    simp only [H3, mem_filter, mem_univ, true_and, G_degree]
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  · intro x hx y hy hxy
    rw [G_adj] at hxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      exact absurd hxy (by decide)

/-! ### `γ_2(G) = 5` -/

/-- Whether `{a, b, c, d}` is 2-dominating, computed from the Boolean adjacency. -/
def twoDomB (a b c d : Fin 12) : Bool :=
  (List.finRange 12).all fun v =>
    v == a || v == b || v == c || v == d ||
      Nat.ble 2 (cond (adjB v a) 1 0 + cond (adjB v b) 1 0 + cond (adjB v c) 1 0 +
        cond (adjB v d) 1 0)

/-- Four distinct vertices forming a 2-dominating set. -/
def badB (a b c d : Fin 12) : Bool :=
  (a != b) && (a != c) && (a != d) && (b != c) && (b != d) && (c != d) && twoDomB a b c d

lemma badB_false : ∀ a b c d : Fin 12, badB a b c d = false := by decide

/-- No four vertices form a 2-dominating set. -/
lemma not_twoDom_four (a b c d : Fin 12) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ¬ IsTwoDom G {a, b, c, d} := by
  intro h
  have htrue : twoDomB a b c d = true := by
    rw [twoDomB, List.all_eq_true]
    intro v _
    by_cases hvS : v ∈ ({a, b, c, d} : Finset (Fin 12))
    · simp only [mem_insert, mem_singleton] at hvS
      rcases hvS with rfl | rfl | rfl | rfl <;> simp
    · have h2 := h v hvS
      have e1 := card_filter_insert_le (G.Adj v) a {b, c, d}
      have e2 := card_filter_insert_le (G.Adj v) b {c, d}
      have e3 := card_filter_insert_le (G.Adj v) c {d}
      have e4 : #(({d} : Finset (Fin 12)).filter (G.Adj v)) ≤ if G.Adj v d then 1 else 0 := by
        rw [filter_singleton]
        split_ifs <;> simp
      simp only [G_adj] at e1 e2 e3 e4 h2
      rw [cond_eq, cond_eq, cond_eq, cond_eq]
      simp only [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq]
      right
      omega
  have hne : ∀ x y : Fin 12, x ≠ y → (x != y) = true := fun x y h => bne_iff_ne.mpr h
  have := badB_false a b c d
  rw [badB, htrue, hne a b hab, hne a c hac, hne a d had, hne b c hbc, hne b d hbd,
    hne c d hcd] at this
  exact Bool.false_ne_true this.symm

lemma G_twoDomNum : 5 ≤ twoDomNum G := by
  have hne : {k | ∃ S, IsTwoDom G S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  rw [twoDomNum, ← hcard]
  by_contra hlt
  push Not at hlt
  -- enlarge `S` to exactly four vertices
  obtain ⟨T, hST, hT⟩ := exists_superset_card_eq (s := S) (n := 4) (by omega) (by simp)
  have hTdom : IsTwoDom G T := by
    intro v hv
    exact (hS v fun h => hv (hST h)).trans (card_le_card (filter_subset_filter _ hST))
  obtain ⟨a, T', haT', rfl, hT'⟩ := card_eq_succ.mp hT
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := card_eq_three.mp hT'
  simp only [mem_insert, mem_singleton, not_or] at haT'
  exact not_twoDom_four a b c d haT'.1 haT'.2.1 haT'.2.2 hbc hbd hcd hTdom

/-- **WOWII Conjecture 399b is false.** -/
theorem not_conjecture399b : ¬ Conjecture399b := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le (by norm_num) G_alphaIn)] at h1
  have := G_WP
  have := G_twoDomNum
  omega

end WOWII399b
