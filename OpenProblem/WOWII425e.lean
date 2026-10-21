import OpenProblem.WOWII425d
import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 425e is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 425e.** Let `G` be a connected graph on `n > 3` vertices and `D` the set of
> neighbor dominators of `G`. Then `i(G) ≤ 4|T_min(G)| + |E(G[D])|`.

Here `i` is the independent domination number and `T_min(G)` is the set of vertices incident with
the fewest triangles. Following DeLaViña and Pepper, a vertex `v` is a *neighbor dominator* if
`N[u] ⊆ N[v]` for some vertex `u ≠ v`.

The counterexample `G` has 12 vertices and 27 edges and was found by simulated annealing.

* No vertex is a neighbor dominator, so `|E(G[D])| = 0`.
* Vertex `10` lies in no triangle, and every other vertex lies in at least one, so
  `|T_min| = 1`.

So the bound is `4`. A finite check shows that no independent set with at most four vertices
dominates `G`, so `i(G) ≥ 5`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII425e

open WOWII179 WOWII422b WOWII426 WOWII449 WOWII425d

variable {V : Type*} [Fintype V]

/-- The neighbor dominators: vertices `v` with `N[u] ⊆ N[v]` for some vertex `u ≠ v`. -/
def nbrDom (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => ∃ u, u ≠ v ∧ ∀ w, (w = u ∨ G.Adj u w) → (w = v ∨ G.Adj v w)

/-- The statement of Conjecture 425e. -/
def Conjecture425e : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    indepDomNum G ≤ 4 * #(Tmin G) + edgesIn G (nbrDom G)

lemma edgesIn_empty (G : SimpleGraph V) : edgesIn G ∅ = 0 := by
  rw [edgesIn, card_eq_zero, filter_eq_empty_iff]
  intro e _ h
  exact notMem_empty _ (h _ (Sym2.out_fst_mem e))

/-! ### The counterexample -/

def E : List (Fin 12 × Fin 12) :=
  [(0, 2), (0, 5), (0, 6), (1, 7), (1, 9), (1, 11), (2, 7), (2, 9), (2, 10), (2, 11), (3, 4),
    (3, 6), (3, 7), (4, 5), (4, 9), (5, 6), (5, 7), (5, 9), (5, 11), (6, 7), (6, 9), (6, 10),
    (6, 11), (7, 8), (7, 9), (8, 9), (8, 11)]

def adjB (a b : Fin 12) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 12} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨7, fun w => ?_⟩
  by_cases hw : w = 7
  · rw [hw]
  by_cases h1 : adjB 7 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 7 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

/-- No vertex of `G` is a neighbor dominator. -/
lemma G_nbrDom : nbrDom G = ∅ := by
  have key : ∀ v u : Fin 12,
      u = v ∨ ∃ w, (w = u ∨ adjB u w = true) ∧ ¬(w = v ∨ adjB v w = true) := by decide
  rw [eq_empty_iff_forall_notMem]
  intro v hv
  simp only [nbrDom, mem_filter, mem_univ, true_and] at hv
  obtain ⟨u, huv, hsub⟩ := hv
  rcases key v u with h | ⟨w, hw1, hw2⟩
  · exact huv h
  · apply hw2
    rcases hsub w (hw1.imp id G_adj.mpr) with h | h
    · exact Or.inl h
    · exact Or.inr (G_adj.mp h)

/-- The triangle count from the Boolean adjacency. -/
def numTriB (v : Fin 12) : ℕ :=
  #((univ.filter fun w => adjB v w = true).powersetCard 2 |>.filter fun s =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → adjB a b = true)

lemma numTri_eq (v : Fin 12) : numTri G v = numTriB v := by
  have hN : G.neighborFinset v = univ.filter fun w => adjB v w = true := by
    ext w
    simp [G_adj]
  rw [numTri, numTriB, hN]
  congr 1
  ext s
  simp only [mem_filter, G_adj]

lemma G_Tmin : #(Tmin G) = 1 := by
  have h10 : numTri G 10 = 0 := by rw [numTri_eq]; decide
  have hpos : ∀ v : Fin 12, v ≠ 10 → 1 ≤ numTri G v := by
    intro v hv
    rw [numTri_eq]
    revert v
    decide
  rw [card_eq_one]
  refine ⟨10, ?_⟩
  ext v
  simp only [Tmin, mem_filter, mem_univ, true_and, mem_singleton]
  have hinf : ∀ w : Fin 12, univ.inf' ⟨w, mem_univ w⟩ (numTri G) = 0 := fun w =>
    Nat.eq_zero_of_le_zero ((inf'_le _ (mem_univ 10)).trans h10.le)
  rw [hinf v]
  constructor
  · intro h
    by_contra hv
    have := hpos v hv
    omega
  · rintro rfl
    exact h10

/-- Whether `{a, b, c, d}` (repetitions allowed) is an independent dominating set. -/
def badB (a b c d : Fin 12) : Bool :=
  (!adjB a b && !adjB a c && !adjB a d && !adjB b c && !adjB b d && !adjB c d) &&
    (List.finRange 12).all fun v =>
      v == a || v == b || v == c || v == d || adjB v a || adjB v b || adjB v c || adjB v d

lemma badB_false : ∀ a b c d : Fin 12, badB a b c d = false := by decide

lemma G_indepDomNum : 5 ≤ indepDomNum G := by
  have hne : {k | ∃ S, IsDom G S ∧ IsIndep G S ∧ #S = k}.Nonempty := by
    obtain ⟨I, -, hI, hImax⟩ := exists_maximal_indep G ∅ (fun x hx => absurd hx (notMem_empty x))
    refine ⟨_, I, fun x => ?_, hI, rfl⟩
    by_cases hx : x ∈ I
    · exact Or.inl hx
    · exact Or.inr (hImax x hx)
  obtain ⟨S, hD, hI, hcard⟩ := Nat.sInf_mem hne
  rw [indepDomNum, ← hcard]
  by_contra hlt
  push Not at hlt
  have hdom : ∀ v, v ∈ S ∨ ∃ u ∈ S, adjB v u = true := fun v => by
    rcases hD v with h | ⟨u, hu, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, G_adj.mp h⟩
  have hS0 : S.Nonempty := by
    rcases hdom 0 with h | ⟨u, hu, -⟩
    · exact ⟨0, h⟩
    · exact ⟨u, hu⟩
  obtain ⟨a, b, c, d, hSeq⟩ : ∃ a b c d : Fin 12, S = {a, b, c, d} := by
    interval_cases hk : #S
    · exact absurd hS0 (by rw [card_eq_zero.mp hk]; simp)
    · obtain ⟨a, ha⟩ := card_eq_one.mp hk
      exact ⟨a, a, a, a, by rw [ha]; simp⟩
    · obtain ⟨a, b, -, hab⟩ := card_eq_two.mp hk
      exact ⟨a, b, b, b, by rw [hab]; simp⟩
    · obtain ⟨a, b, c, -, -, -, habc⟩ := card_eq_three.mp hk
      exact ⟨a, b, c, c, by rw [habc]; simp⟩
    · obtain ⟨a, T, -, hT, hTc⟩ := card_eq_succ.mp hk
      obtain ⟨b, c, d, -, -, -, rfl⟩ := card_eq_three.mp hTc
      exact ⟨a, b, c, d, hT.symm⟩
  subst hSeq
  have hind : ∀ x ∈ ({a, b, c, d} : Finset (Fin 12)), ∀ y ∈ ({a, b, c, d} : Finset (Fin 12)),
      adjB x y = false := fun x hx y hy => by
    by_contra h
    exact hI x hx y hy (G_adj.mpr (by simpa using h))
  have htrue : badB a b c d = true := by
    simp only [badB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_finRange,
      true_implies, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨hind a (by simp) b (by simp), hind a (by simp) c (by simp)⟩,
      hind a (by simp) d (by simp)⟩, hind b (by simp) c (by simp)⟩,
      hind b (by simp) d (by simp)⟩, hind c (by simp) d (by simp)⟩, fun v => ?_⟩
    rcases hdom v with h | ⟨u, hu, h⟩
    · simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp
    · simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> simp [h]
  rw [badB_false] at htrue
  exact Bool.false_ne_true htrue

/-- **WOWII Conjecture 425e is false.** -/
theorem not_conjecture425e : ¬ Conjecture425e := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [G_Tmin, G_nbrDom, edgesIn_empty] at h1
  have := G_indepDomNum
  omega

end WOWII425e
