import OpenProblem.WOWII320
import OpenProblem.WOWII179

/-!
# Written on the Wall II, Conjecture 319 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 319.** Let `G` be a simple connected graph with `n > 1`. If
> `max_v dist_even(v) = γ(G)`, then `G` is well totally dominated.

Here `dist_even(v)` is the number of vertices at even distance from `v`, counting `v` itself (as
in formal-conjectures' `SimpleGraph.distEven`), `γ` is the domination number, and `G` is *well
totally dominated* if all minimal total dominating sets have the same size.

The conjecture fails for a connected graph on 10 vertices with 12 edges (graph6 `I?`D@`WH_`):

* every vertex has exactly four vertices at even distance (`G_distEven`);
* the domination number is four (`G_domNum`);
* `{1, 2, 6, 8}` and `{0, 1, 3, 6, 8}` are minimal total dominating sets (`S₁_min`, `S₂_min`).

So `max dist_even = γ = 4`, but `G` is not well totally dominated (`not_conjecture319`). An
exhaustive search shows that every connected graph on at most 9 vertices satisfying the hypothesis
is well totally dominated, so this counterexample has the least possible order.

Distances are certified by breadth-first search tables (`dist_eq_of_bfs`): a labelling `f` with
`f v = 0`, which changes by at most one along every edge and in which every other vertex has a
neighbour with a smaller label, is the distance from `v`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII319

open WOWII179 WOWII320 WOWII326 WOWII372

/-- The statement of Conjecture 319. -/
def Conjecture319 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 1 < Fintype.card V →
    univ.sup (distEven G) = domNum G → WellTotallyDominated G

/-! ### Distances from breadth-first search tables -/

/-- A breadth-first search labelling from `v` gives the distances from `v`. -/
theorem dist_eq_of_bfs {V : Type*} (G : SimpleGraph V) (v : V) (f : V → ℕ) (h0 : f v = 0)
    (h0' : ∀ u, f u = 0 → u = v) (hlip : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (hpred : ∀ u, f u ≠ 0 → ∃ w, G.Adj w u ∧ f w + 1 = f u) (u : V) :
    G.Reachable v u ∧ G.dist v u = f u := by
  -- labels grow by at most one along a walk
  have hwalk : ∀ a b (p : G.Walk a b), f b ≤ f a + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | cons h p ih =>
      have := hlip _ _ h
      rw [Walk.length_cons]
      omega
  -- a walk of length `f u`
  have hle : ∀ k u, f u = k → ∃ p : G.Walk v u, p.length = k := by
    intro k
    induction k with
    | zero => intro u hu; rw [h0' u hu]; exact ⟨Walk.nil, rfl⟩
    | succ k ih =>
      intro u hu
      obtain ⟨w, hwu, hw⟩ := hpred u (by omega)
      obtain ⟨p, hp⟩ := ih w (by omega)
      exact ⟨p.concat hwu, by rw [Walk.length_concat, hp]⟩
  obtain ⟨p, hp⟩ := hle (f u) u rfl
  refine ⟨p.reachable, le_antisymm (hp ▸ dist_le p) ?_⟩
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  have := hwalk v u q
  omega

/-! ### The counterexample -/

/-- The edges of the counterexample. -/
def E : List (Fin 10 × Fin 10) :=
  [(0, 4), (0, 6), (1, 5), (1, 8), (2, 6), (2, 7), (2, 9), (3, 7), (3, 8), (4, 8), (5, 9),
    (6, 9)]

/-- Adjacency in the counterexample. -/
def adjB (a b : Fin 10) : Bool := E.contains (a, b) || E.contains (b, a)

/-- The counterexample, with graph6 code `I?`D@`WH_`. -/
def G : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 10} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 10, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

/-- The distances in `G`. -/
def D : Fin 10 → Fin 10 → ℕ :=
  ![![0, 3, 2, 3, 1, 3, 1, 3, 2, 2],
    ![3, 0, 3, 2, 2, 1, 3, 3, 1, 2],
    ![2, 3, 0, 2, 3, 2, 1, 1, 3, 1],
    ![3, 2, 2, 0, 2, 3, 3, 1, 1, 3],
    ![1, 2, 3, 2, 0, 3, 2, 3, 1, 3],
    ![3, 1, 2, 3, 3, 0, 2, 3, 2, 1],
    ![1, 3, 1, 3, 2, 2, 0, 2, 3, 1],
    ![3, 3, 1, 1, 3, 3, 2, 0, 2, 2],
    ![2, 1, 3, 1, 1, 2, 3, 2, 0, 3],
    ![2, 2, 1, 3, 3, 1, 1, 2, 3, 0]]

lemma G_dist (v u : Fin 10) : G.Reachable v u ∧ G.dist v u = D v u := by
  refine dist_eq_of_bfs G v (D v) ?_ ?_ ?_ ?_ u
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

lemma G_distEven (v : Fin 10) : distEven G v = 4 := by
  simp only [distEven, fun u => (G_dist v u).2]
  revert v
  decide

lemma G_sup_distEven : univ.sup (distEven G) = 4 := by
  apply le_antisymm
  · exact Finset.sup_le fun v _ => (G_distEven v).le
  · exact (G_distEven 0).symm.le.trans (le_sup (f := distEven G) (mem_univ 0))

lemma isDom_iff (S : Finset (Fin 10)) :
    IsDom G S ↔ ∀ v, v ∈ S ∨ ∃ u ∈ S, adjB v u = true := by
  simp only [IsDom, G_adj]

lemma G_domNum : domNum G = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨{0, 1, 2, 3}, (isDom_iff _).mpr (by decide), rfl⟩
  · refine le_csInf ⟨10, univ, fun v => Or.inl (mem_univ v), by simp⟩ ?_
    rintro k ⟨S, hS, rfl⟩
    by_contra hlt
    push Not at hlt
    have h3 : ∀ a b c : Fin 10, ¬ ∀ v, v ∈ ({a, b, c} : Finset (Fin 10)) ∨
        ∃ u ∈ ({a, b, c} : Finset (Fin 10)), adjB v u = true := by decide
    have h0 : #S ≠ 0 := by
      rw [Ne, card_eq_zero]
      rintro rfl
      simpa using (isDom_iff ∅).mp hS 0
    -- every set of at most three vertices lies in some `{a, b, c}`
    obtain ⟨a, b, c, hsub⟩ : ∃ a b c, S ⊆ {a, b, c} := by
      rcases (by omega : #S = 1 ∨ #S = 2 ∨ #S = 3) with h | h | h
      · obtain ⟨x, rfl⟩ := card_eq_one.mp h
        exact ⟨x, x, x, by simp⟩
      · obtain ⟨x, y, -, rfl⟩ := card_eq_two.mp h
        exact ⟨x, y, y, fun z hz => by simp at hz ⊢; tauto⟩
      · obtain ⟨x, y, z, -, -, -, rfl⟩ := card_eq_three.mp h
        exact ⟨x, y, z, subset_refl _⟩
    refine h3 a b c fun v => ?_
    rcases (isDom_iff S).mp hS v with h | ⟨u, hu, huv⟩
    · exact Or.inl (hsub h)
    · exact Or.inr ⟨u, hsub hu, huv⟩

lemma isTDS_iff (S : Finset (Fin 10)) : IsTDS G S ↔ ∀ v, ∃ u ∈ S, adjB v u = true := by
  simp only [IsTDS, G_adj]

lemma isMinTDS_of (S : Finset (Fin 10)) (h1 : ∀ v, ∃ u ∈ S, adjB v u = true)
    (h2 : ∀ T ∈ S.powerset, T ≠ S → ¬ ∀ v, ∃ u ∈ T, adjB v u = true) : IsMinTDS G S := by
  refine ⟨(isTDS_iff S).mpr h1, fun T hT hTDS => ?_⟩
  exact h2 T (mem_powerset.mpr hT.1) hT.ne ((isTDS_iff T).mp hTDS)

lemma S₁_min : IsMinTDS G {1, 2, 6, 8} := isMinTDS_of _ (by decide +kernel) (by decide +kernel)

lemma S₂_min : IsMinTDS G {0, 1, 3, 6, 8} :=
  isMinTDS_of _ (by decide +kernel) (by decide +kernel)

/-- **WOWII Conjecture 319 is false.** -/
theorem not_conjecture319 : ¬ Conjecture319 := by
  intro h
  have := h (Fin 10) G G_connected (by simp) (by rw [G_sup_distEven, G_domNum]) _ _ S₁_min S₂_min
  simp at this

end WOWII319
