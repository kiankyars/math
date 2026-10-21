import OpenProblem.WOWII179
import OpenProblem.WOWII267

/-!
# Written on the Wall II, Conjecture 422b is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 422b.** Let `G` be a connected graph on `n > 3` vertices and `M` the vertices of
> maximum degree. Then `i(G) ≤ α(G[M]) + γ(G[V - M])^2`.

Here `i` is the independent domination number, `α` the independence number and `γ` the
domination number.

The counterexample `G` has 14 vertices and 31 edges and was found by simulated annealing.

* Vertex `1` is the unique vertex of maximum degree `8`, so `α(G[M]) = 1`.
* `{0, 9}` dominates `G - 1`, so the bound is at most `1 + 2^2 = 5`.

But `i(G) = 6`. Let `I` be an independent dominating set.

* If `9 ∈ I`, then `I` avoids `N(9) = {0, 1, 4, 5, 6, 7, 11}`. The vertices `2, 8, 12, 13` have
  all their neighbours there, so they lie in `I`. One of the adjacent vertices `3` and `10` lies
  in `I` as well, so `|I| ≥ 6`.
* If `9 ∉ I`, then the leaf `4` lies in `I`. The rest of `I` is an independent dominating set of
  `G - {4, 9}`, and a finite check shows these have at least five vertices.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII422b

open WOWII179

variable {V : Type*} [Fintype V]

/-- `S` is independent. -/
def IsIndep (G : SimpleGraph V) (S : Finset V) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

/-- The independent domination number `i(G)`. -/
def indepDomNum (G : SimpleGraph V) : ℕ := sInf {k | ∃ S, IsDom G S ∧ IsIndep G S ∧ #S = k}

/-- The vertices of maximum degree. -/
def maxDegSet (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = G.maxDegree

/-- The statement of Conjecture 422b. -/
def Conjecture422b : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    indepDomNum G ≤ (G.induce (maxDegSet G : Set V)).indepNum +
      domNum (G.induce ((maxDegSet G)ᶜ : Set V)) ^ 2

/-! ### The counterexample -/

def E : List (Fin 14 × Fin 14) :=
  [(0, 2), (0, 3), (0, 8), (0, 9), (0, 10), (0, 12), (0, 13), (1, 2), (1, 3), (1, 5), (1, 8),
    (1, 9), (1, 10), (1, 12), (1, 13), (2, 7), (3, 10), (4, 9), (5, 8), (5, 9), (5, 10), (5, 12),
    (6, 8), (6, 9), (6, 12), (7, 8), (7, 9), (7, 12), (8, 11), (9, 11), (11, 12)]

def adjB (a b : Fin 14) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 14) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 14} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 14, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 14) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨9, fun w => ?_⟩
  by_cases hw : w = 9
  · rw [hw]
  by_cases h1 : adjB 9 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 9 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

lemma G_maxDegree : G.maxDegree = 8 := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rw [G_degree]
    revert v
    decide
  · have : G.degree 1 = 8 := by rw [G_degree]; decide
    rw [← this]
    exact G.degree_le_maxDegree 1

lemma G_maxDegSet : maxDegSet G = {1} := by
  ext v
  simp only [maxDegSet, mem_filter, mem_univ, true_and, G_maxDegree, G_degree, mem_singleton]
  revert v
  decide

lemma G_alpha : (G.induce (maxDegSet G : Set (Fin 14))).indepNum ≤ 1 := by
  obtain ⟨s, hs⟩ := (G.induce (maxDegSet G : Set (Fin 14))).exists_isNIndepSet_indepNum
  rw [← hs.card_eq, card_le_one]
  intro a _ b _
  have ha := a.2
  have hb := b.2
  simp only [G_maxDegSet, coe_singleton, Set.mem_singleton_iff] at ha hb
  exact Subtype.ext (ha.trans hb.symm)

lemma G_domNum : domNum (G.induce ((maxDegSet G)ᶜ : Set (Fin 14))) ≤ 2 := by
  rw [G_maxDegSet]
  have h0 : (0 : Fin 14) ∈ (({1} : Finset (Fin 14))ᶜ : Set (Fin 14)) := by simp
  have h9 : (9 : Fin 14) ∈ (({1} : Finset (Fin 14))ᶜ : Set (Fin 14)) := by simp
  let S : Finset ((({1} : Finset (Fin 14))ᶜ : Set (Fin 14))) := {⟨0, h0⟩, ⟨9, h9⟩}
  have hS : IsDom (G.induce ((({1} : Finset (Fin 14))ᶜ : Set (Fin 14)))) S := by
    intro v
    have key : ∀ x : Fin 14, x ≠ 1 → x = 0 ∨ x = 9 ∨ adjB x 0 = true ∨ adjB x 9 = true := by
      decide
    have hv : v.1 ≠ 1 := by simpa using v.2
    rcases key v.1 hv with h | h | h | h
    · exact Or.inl (by simp [S, Subtype.ext_iff, h])
    · exact Or.inl (by simp [S, Subtype.ext_iff, h])
    · exact Or.inr ⟨⟨0, h0⟩, by simp [S], by simpa [comap_adj, G_adj] using h⟩
    · exact Or.inr ⟨⟨9, h9⟩, by simp [S], by simpa [comap_adj, G_adj] using h⟩
  exact (domNum_le hS).trans card_le_two

/-- Whether the set `{a, b, c, d}` (with repetitions allowed) is independent and dominates
`G - {4, 9}`. -/
def badB (a b c d : Fin 14) : Bool :=
  (!adjB a b && !adjB a c && !adjB a d && !adjB b c && !adjB b d && !adjB c d) &&
    (List.finRange 14).all fun v =>
      v == 4 || v == 9 || v == a || v == b || v == c || v == d ||
        adjB v a || adjB v b || adjB v c || adjB v d

/-- `badB` restricted to vertices other than `4` and `9`. -/
def badB' (a b c d : Fin 14) : Bool :=
  (a != 4 && a != 9 && b != 4 && b != 9 && c != 4 && c != 9 && d != 4 && d != 9) && badB a b c d

lemma badB'_false : ∀ a b c d : Fin 14, badB' a b c d = false := by decide

/-- Every independent dominating set of `G` has at least six vertices. -/
lemma card_ge {I : Finset (Fin 14)} (hD : IsDom G I) (hI : IsIndep G I) : 6 ≤ #I := by
  have hdom : ∀ v, v ∈ I ∨ ∃ u ∈ I, adjB v u = true := fun v => by
    rcases hD v with h | ⟨u, hu, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, G_adj.mp h⟩
  have hind : ∀ x ∈ I, ∀ y ∈ I, adjB x y = false := fun x hx y hy => by
    by_contra h
    exact hI x hx y hy (G_adj.mpr (by simpa using h))
  by_cases h9 : (9 : Fin 14) ∈ I
  · -- the neighbours of `9` are excluded, which forces `2, 8, 12, 13` into `I`
    have hN9 : ∀ u ∈ I, adjB 9 u = false := fun u hu => hind 9 h9 u hu
    have forced : ∀ v : Fin 14, (∀ u, adjB v u = true → adjB 9 u = true) → v ∈ I := by
      intro v hv
      rcases hdom v with h | ⟨u, hu, h⟩
      · exact h
      · have := hN9 u hu
        rw [hv u h] at this
        exact absurd this (by decide)
    have h2 := forced 2 (by decide)
    have h8 := forced 8 (by decide)
    have h12 := forced 12 (by decide)
    have h13 := forced 13 (by decide)
    have h310 : (3 : Fin 14) ∈ I ∨ (10 : Fin 14) ∈ I := by
      rcases hdom 3 with h | ⟨u, hu, h⟩
      · exact Or.inl h
      · have hu' : u = 0 ∨ u = 1 ∨ u = 10 :=
          (by decide : ∀ u : Fin 14, adjB 3 u = true → u = 0 ∨ u = 1 ∨ u = 10) u h
        rcases hu' with rfl | rfl | rfl
        · exact absurd (hN9 0 hu) (by decide)
        · exact absurd (hN9 1 hu) (by decide)
        · exact Or.inr hu
    rcases h310 with h3 | h10
    · have := card_le_card (show ({9, 2, 8, 12, 13, 3} : Finset (Fin 14)) ⊆ I by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      exact this.trans' (by decide)
    · have := card_le_card (show ({9, 2, 8, 12, 13, 10} : Finset (Fin 14)) ⊆ I by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      exact this.trans' (by decide)
  · -- the leaf `4` lies in `I`, and the rest dominates `G - {4, 9}`
    have h4 : (4 : Fin 14) ∈ I := by
      rcases hdom 4 with h | ⟨u, hu, h⟩
      · exact h
      · have : u = 9 := (by decide : ∀ u : Fin 14, adjB 4 u = true → u = 9) u h
        exact absurd (this ▸ hu) h9
    set J := I.erase 4
    have hJ : ∀ x ∈ J, x ≠ 4 ∧ x ≠ 9 := fun x hx =>
      ⟨(mem_erase.mp hx).1, fun h => h9 (h ▸ (mem_erase.mp hx).2)⟩
    have hcardI : #I = #J + 1 := by rw [card_erase_of_mem h4]; have := card_pos.mpr ⟨4, h4⟩; omega
    by_contra hlt
    have hJ4 : #J ≤ 4 := by omega
    -- write `J` as `{a, b, c, d}` with repetitions
    obtain ⟨a, b, c, d, hJeq⟩ : ∃ a b c d : Fin 14, J = {a, b, c, d} := by
      rcases Nat.lt_or_ge #J 1 with h0 | h1
      · -- `J = ∅`: then vertex `0` is not dominated
        exfalso
        have hJe : J = ∅ := card_eq_zero.mp (by omega)
        rcases hdom 0 with h | ⟨u, hu, h⟩
        · have : (0 : Fin 14) ∈ J := mem_erase.mpr ⟨by decide, h⟩
          simp [hJe] at this
        · have hu4 : u ≠ 4 := fun h' => by rw [h'] at h; exact absurd h (by decide)
          have : u ∈ J := mem_erase.mpr ⟨hu4, hu⟩
          simp [hJe] at this
      · interval_cases hk : #J
        · obtain ⟨a, ha⟩ := card_eq_one.mp hk
          exact ⟨a, a, a, a, by rw [ha]; simp⟩
        · obtain ⟨a, b, -, hab⟩ := card_eq_two.mp hk
          exact ⟨a, b, b, b, by rw [hab]; simp⟩
        · obtain ⟨a, b, c, -, -, -, habc⟩ := card_eq_three.mp hk
          exact ⟨a, b, c, c, by rw [habc]; simp⟩
        · obtain ⟨a, T, haT, hT, hTc⟩ := card_eq_succ.mp hk
          obtain ⟨b, c, d, -, -, -, rfl⟩ := card_eq_three.mp hTc
          exact ⟨a, b, c, d, hT.symm⟩
    have ha := hJ a (by rw [hJeq]; simp)
    have hb := hJ b (by rw [hJeq]; simp)
    have hc := hJ c (by rw [hJeq]; simp)
    have hd := hJ d (by rw [hJeq]; simp)
    have hbad : badB a b c d = true := by
      have hJI : J ⊆ I := erase_subset 4 I
      have mem : ∀ x ∈ ({a, b, c, d} : Finset (Fin 14)), x ∈ I := fun x hx => hJI (hJeq ▸ hx)
      have hi : ∀ x ∈ ({a, b, c, d} : Finset (Fin 14)), ∀ y ∈ ({a, b, c, d} : Finset (Fin 14)),
          adjB x y = false := fun x hx y hy => hind x (mem x hx) y (mem y hy)
      simp only [badB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_finRange,
        true_implies, Bool.or_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨⟨⟨hi a (by simp) b (by simp), hi a (by simp) c (by simp)⟩,
        hi a (by simp) d (by simp)⟩, hi b (by simp) c (by simp)⟩, hi b (by simp) d (by simp)⟩,
        hi c (by simp) d (by simp)⟩, fun v => ?_⟩
      by_cases hv49 : v = 4 ∨ v = 9
      · rcases hv49 with h | h <;> simp [h]
      push Not at hv49
      rcases hdom v with h | ⟨u, hu, h⟩
      · have hvJ : v ∈ J := mem_erase.mpr ⟨hv49.1, h⟩
        rw [hJeq] at hvJ
        simp only [mem_insert, mem_singleton] at hvJ
        rcases hvJ with rfl | rfl | rfl | rfl <;> simp
      · have hu4 : u ≠ 4 := by
          rintro rfl
          have : v = 9 := (by decide : ∀ v : Fin 14, adjB v 4 = true → v = 9) v h
          exact hv49.2 this
        have huJ : u ∈ J := mem_erase.mpr ⟨hu4, hu⟩
        rw [hJeq] at huJ
        simp only [mem_insert, mem_singleton] at huJ
        rcases huJ with rfl | rfl | rfl | rfl <;> simp [h]
    have hne : ∀ x y : Fin 14, x ≠ y → (x != y) = true := fun x y h => bne_iff_ne.mpr h
    have := badB'_false a b c d
    rw [badB', hbad, hne a 4 ha.1, hne a 9 ha.2, hne b 4 hb.1, hne b 9 hb.2, hne c 4 hc.1,
      hne c 9 hc.2, hne d 4 hd.1, hne d 9 hd.2] at this
    exact Bool.false_ne_true this.symm

lemma G_indepDomNum : 6 ≤ indepDomNum G := by
  have hne : {k | ∃ S, IsDom G S ∧ IsIndep G S ∧ #S = k}.Nonempty := by
    obtain ⟨I, hI⟩ : ∃ I : Finset (Fin 14), IsDom G I ∧ IsIndep G I := by
      refine ⟨{9, 2, 8, 12, 13, 3}, ?_, ?_⟩
      · intro v
        have key : ∀ v : Fin 14, v ∈ ({9, 2, 8, 12, 13, 3} : Finset (Fin 14)) ∨
            ∃ u ∈ ({9, 2, 8, 12, 13, 3} : Finset (Fin 14)), adjB v u = true := by decide
        rcases key v with h | ⟨u, hu, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, hu, G_adj.mpr h⟩
      · intro x hx y hy hxy
        have key : ∀ x ∈ ({9, 2, 8, 12, 13, 3} : Finset (Fin 14)),
            ∀ y ∈ ({9, 2, 8, 12, 13, 3} : Finset (Fin 14)), adjB x y = false := by decide
        rw [G_adj, key x hx y hy] at hxy
        exact Bool.false_ne_true hxy
    exact ⟨_, I, hI.1, hI.2, rfl⟩
  obtain ⟨S, hD, hI, hcard⟩ := Nat.sInf_mem hne
  rw [indepDomNum, ← hcard]
  exact card_ge hD hI

/-- **WOWII Conjecture 422b is false.** -/
theorem not_conjecture422b : ¬ Conjecture422b := by
  intro h
  have h1 := h (Fin 14) G G_connected (by simp)
  have h2 := G_alpha
  have h3 := G_domNum
  have h4 := G_indepDomNum
  have h5 : domNum (G.induce ((maxDegSet G)ᶜ : Set (Fin 14))) ^ 2 ≤ 4 := by
    calc _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 4 := by norm_num
  omega

end WOWII422b
