import OpenProblem.WOWII426
import OpenProblem.WOWII444

/-!
# Written on the Wall II, Conjecture 425d is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 425d.** Let `G` be a connected graph on `n > 3` vertices and `P` the set of
> pendants of `G`. Then `i(G) ≤ |T_min(G)| + sum of K_4(v) + γ(G[V-N(P)])`.

Here `i` is the independent domination number, `T_min(G)` the set of vertices incident with the
fewest triangles, `K_4(v)` the number of copies of `K_4` containing `v`, and `γ` the domination
number.

The counterexample `G` has 12 vertices and 26 edges and was found by simulated annealing.

* `G` has no pendant, so `V - N(P) = V`, and `{0, 7}` dominates `G`.
* `G` contains no `K_4`.
* Vertex `2` lies in no triangle, and every other vertex lies in at least one, so
  `|T_min| = 1`.

So the bound is at most `1 + 0 + 2 = 3`. A finite check shows that no independent set with at most
three vertices dominates `G`, so `i(G) ≥ 4`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII425d

open WOWII179 WOWII422b WOWII426 WOWII444

variable {V : Type*} [Fintype V]

/-- The number of triangles at `v`. -/
def numTri (G : SimpleGraph V) (v : V) : ℕ :=
  #((G.neighborFinset v).powersetCard 2 |>.filter fun s => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b)

/-- The vertices incident with the fewest triangles. -/
def Tmin (G : SimpleGraph V) : Finset V := univ.filter fun v => numTri G v = univ.inf' ⟨v, mem_univ v⟩ (numTri G)

/-- The pendant vertices. -/
def pend (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = 1

/-- The statement of Conjecture 425d. -/
def Conjecture425d : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    indepDomNum G ≤ #(Tmin G) + ∑ v, numK4 G v + domNum (G.induce ((nbhd G (pend G))ᶜ : Set V))

/-! ### The counterexample -/

def E : List (Fin 12 × Fin 12) :=
  [(0, 2), (0, 3), (0, 6), (0, 7), (0, 10), (0, 11), (1, 2), (1, 7), (1, 9), (1, 10), (1, 11),
    (2, 4), (3, 4), (3, 7), (3, 8), (3, 10), (3, 11), (4, 5), (4, 7), (5, 7), (5, 9), (5, 11),
    (6, 11), (7, 8), (7, 9), (9, 10)]

def adjB (a b : Fin 12) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 12} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 12) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

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

lemma G_pend : pend G = ∅ := by
  ext v
  simp only [pend, mem_filter, mem_univ, true_and, G_degree, notMem_empty, iff_false]
  revert v
  decide

lemma G_domNum : domNum (G.induce ((nbhd G (pend G))ᶜ : Set (Fin 12))) ≤ 2 := by
  have hmem : ∀ x : Fin 12, x ∈ ((nbhd G (pend G))ᶜ : Set (Fin 12)) := by
    intro x
    simp [nbhd, G_pend]
  let S : Finset ((nbhd G (pend G))ᶜ : Set (Fin 12)) := {⟨0, hmem 0⟩, ⟨7, hmem 7⟩}
  have hS : IsDom (G.induce ((nbhd G (pend G))ᶜ : Set (Fin 12))) S := by
    intro v
    have key : ∀ x : Fin 12, x = 0 ∨ x = 7 ∨ adjB x 0 = true ∨ adjB x 7 = true := by decide
    rcases key v.1 with h | h | h | h
    · exact Or.inl (by simp [S, Subtype.ext_iff, h])
    · exact Or.inl (by simp [S, Subtype.ext_iff, h])
    · exact Or.inr ⟨⟨0, hmem 0⟩, by simp [S], by simpa [comap_adj, G_adj] using h⟩
    · exact Or.inr ⟨⟨7, hmem 7⟩, by simp [S], by simpa [comap_adj, G_adj] using h⟩
  exact (Nat.sInf_le (s := {k | ∃ S, IsDom _ S ∧ #S = k}) ⟨S, hS, rfl⟩).trans card_le_two

/-- Triangle and `K_4` counts from the Boolean adjacency. -/
def numTriB (v : Fin 12) : ℕ :=
  #((univ.filter fun w => adjB v w = true).powersetCard 2 |>.filter fun s =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → adjB a b = true)

def numK4B (v : Fin 12) : ℕ :=
  #((univ.filter fun w => adjB v w = true).powersetCard 3 |>.filter fun s =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → adjB a b = true)

lemma hN (v : Fin 12) : G.neighborFinset v = univ.filter fun w => adjB v w = true := by
  ext w
  simp [G_adj]

lemma numTri_eq (v : Fin 12) : numTri G v = numTriB v := by
  rw [numTri, numTriB, hN]
  congr 1
  ext s
  simp only [mem_filter, G_adj]

lemma numK4_eq (v : Fin 12) : numK4 G v = numK4B v := by
  rw [numK4, numK4B, hN]
  congr 1
  ext s
  simp only [mem_filter, G_adj]

lemma G_sumK4 : ∑ v, numK4 G v = 0 := by
  rw [show numK4 G = numK4B from funext numK4_eq]
  decide

lemma G_Tmin : #(Tmin G) = 1 := by
  have h2 : numTri G 2 = 0 := by rw [numTri_eq]; decide
  have hpos : ∀ v : Fin 12, v ≠ 2 → 1 ≤ numTri G v := by
    intro v hv
    rw [numTri_eq]
    revert v
    decide
  rw [card_eq_one]
  refine ⟨2, ?_⟩
  ext v
  simp only [Tmin, mem_filter, mem_univ, true_and, mem_singleton]
  have hinf : ∀ w : Fin 12, univ.inf' ⟨w, mem_univ w⟩ (numTri G) = 0 := fun w =>
    Nat.eq_zero_of_le_zero ((inf'_le _ (mem_univ 2)).trans h2.le)
  rw [hinf v]
  constructor
  · intro h
    by_contra hv
    have := hpos v hv
    omega
  · rintro rfl
    exact h2

/-- Whether `{a, b, c}` (repetitions allowed) is an independent dominating set. -/
def badB (a b c : Fin 12) : Bool :=
  (!adjB a b && !adjB a c && !adjB b c) &&
    (List.finRange 12).all fun v => v == a || v == b || v == c || adjB v a || adjB v b || adjB v c

lemma badB_false : ∀ a b c : Fin 12, badB a b c = false := by decide

lemma G_indepDomNum : 4 ≤ indepDomNum G := by
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
  obtain ⟨a, b, c, hSeq⟩ : ∃ a b c : Fin 12, S = {a, b, c} := by
    interval_cases hk : #S
    · exact absurd hS0 (by rw [card_eq_zero.mp hk]; simp)
    · obtain ⟨a, ha⟩ := card_eq_one.mp hk
      exact ⟨a, a, a, by rw [ha]; simp⟩
    · obtain ⟨a, b, -, hab⟩ := card_eq_two.mp hk
      exact ⟨a, b, b, by rw [hab]; simp⟩
    · obtain ⟨a, b, c, -, -, -, habc⟩ := card_eq_three.mp hk
      exact ⟨a, b, c, habc⟩
  subst hSeq
  have hind : ∀ x ∈ ({a, b, c} : Finset (Fin 12)), ∀ y ∈ ({a, b, c} : Finset (Fin 12)),
      adjB x y = false := fun x hx y hy => by
    by_contra h
    exact hI x hx y hy (G_adj.mpr (by simpa using h))
  have htrue : badB a b c = true := by
    simp only [badB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_finRange,
      true_implies, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨⟨hind a (by simp) b (by simp), hind a (by simp) c (by simp)⟩,
      hind b (by simp) c (by simp)⟩, fun v => ?_⟩
    rcases hdom v with h | ⟨u, hu, h⟩
    · simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl | rfl <;> simp
    · simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> simp [h]
  rw [badB_false] at htrue
  exact Bool.false_ne_true htrue

/-- **WOWII Conjecture 425d is false.** -/
theorem not_conjecture425d : ¬ Conjecture425d := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [G_Tmin, G_sumK4] at h1
  have := G_domNum
  have := G_indepDomNum
  omega

end WOWII425d
