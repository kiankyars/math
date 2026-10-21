import Mathlib

/-!
# Written on the Wall II, Conjecture 449

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 449.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ |V \ H_3| + CEILING[(|E(G[H_3])| - 1)/2]`, where `H_3` is the set of vertices of
> degree at least 3.

Here `α_2` is the 2-independence number: the largest order of a set `S` such that every vertex
of `S` has at most one neighbour in `S`.

We prove the conjecture for every finite graph (`conjecture449`). Let `S` be 2-independent, let
`L = V \ H_3`, and let `A = S ∩ H_3`.

* Every `a ∈ A` has degree at least 3 and at most one neighbour in `S`, so it has at least two
  neighbours outside `S`.
* Each vertex of `L \ S` has degree at most 2, so it is adjacent to at most two vertices of `A`.
* The edges from `A` to `H_3 \ S` are distinct edges of `G[H_3]`.

Hence `2|A| ≤ 2|L \ S| + e(H_3)`, and `|S| = |A| + |S ∩ L| ≤ |L| + ⌊e(H_3)/2⌋`. Finally,
`⌊e/2⌋ = ⌈(e - 1)/2⌉` for every natural number `e`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII449

open SimpleGraph

variable {V : Type*} [Fintype V]

/-- `S` is 2-independent: every vertex of `S` has at most one neighbour in `S`. -/
def IsTwoIndep (G : SimpleGraph V) (S : Finset V) : Prop := ∀ v ∈ S, #(S.filter (G.Adj v)) ≤ 1

/-- The 2-independence number `α_2(G)`. -/
def twoIndepNum (G : SimpleGraph V) : ℕ := sSup {k | ∃ S, IsTwoIndep G S ∧ #S = k}

/-- The vertices of degree at least 3. -/
def H3 (G : SimpleGraph V) : Finset V := univ.filter fun v => 3 ≤ G.degree v

/-- The number of edges with both ends in `A`. -/
def edgesIn (G : SimpleGraph V) (A : Finset V) : ℕ := #(G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ A)

lemma bddAbove_twoIndep (G : SimpleGraph V) : BddAbove {k | ∃ S, IsTwoIndep G S ∧ #S = k} :=
  ⟨Fintype.card V, fun _ ⟨S, _, hk⟩ => hk ▸ card_le_univ S⟩

lemma exists_twoIndep (G : SimpleGraph V) : ∃ S, IsTwoIndep G S ∧ #S = twoIndepNum G :=
  Nat.sSup_mem (s := {k | ∃ S, IsTwoIndep G S ∧ #S = k})
    ⟨0, ∅, fun v hv => absurd hv (notMem_empty v), rfl⟩ (bddAbove_twoIndep G)

lemma le_twoIndepNum {G : SimpleGraph V} {S : Finset V} (hS : IsTwoIndep G S) :
    #S ≤ twoIndepNum G :=
  le_csSup (bddAbove_twoIndep G) ⟨S, hS, rfl⟩

/-- The double counting bound `|S| ≤ |V \ H_3| + ⌊e(H_3)/2⌋`. -/
lemma card_le (G : SimpleGraph V) {S : Finset V} (hS : IsTwoIndep G S) :
    #S ≤ #(H3 G)ᶜ + edgesIn G (H3 G) / 2 := by
  set H := H3 G
  set L := Hᶜ
  set A := S ∩ H
  set B := L \ S
  set C := H \ S
  -- every vertex of `A` has at least two neighbours in `B ∪ C`
  have h1 : ∀ a ∈ A, 2 ≤ #(B.filter (G.Adj a)) + #(C.filter (G.Adj a)) := by
    intro a ha
    obtain ⟨haS, haH⟩ := mem_inter.mp ha
    have hdeg : 3 ≤ G.degree a := (mem_filter.mp haH).2
    have hS1 := hS a haS
    have hsplit : G.neighborFinset a ⊆ S.filter (G.Adj a) ∪ (B.filter (G.Adj a) ∪
        C.filter (G.Adj a)) := by
      intro x hx
      rw [mem_neighborFinset] at hx
      simp only [mem_union, mem_filter, B, C, L, mem_sdiff, mem_compl]
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hxS, hx⟩
      · by_cases hxH : x ∈ H
        · exact Or.inr (Or.inr ⟨⟨hxH, hxS⟩, hx⟩)
        · exact Or.inr (Or.inl ⟨⟨hxH, hxS⟩, hx⟩)
    have hc1 := card_union_le (S.filter (G.Adj a)) (B.filter (G.Adj a) ∪ C.filter (G.Adj a))
    have hc2 := card_union_le (B.filter (G.Adj a)) (C.filter (G.Adj a))
    have := card_le_card hsplit
    rw [card_neighborFinset_eq_degree] at this
    omega
  -- the vertices of `B` have degree at most 2
  have h2 : ∑ a ∈ A, #(B.filter (G.Adj a)) ≤ 2 * #B := by
    have hswap : ∑ a ∈ A, #(B.filter (G.Adj a)) = ∑ x ∈ B, #(A.filter (fun a => G.Adj a x)) := by
      simp_rw [card_eq_sum_ones, sum_filter]
      exact sum_comm
    rw [hswap, card_eq_sum_ones B, mul_sum]
    apply sum_le_sum
    intro x hx
    have hxL : x ∈ L := (mem_sdiff.mp hx).1
    have hdeg : G.degree x ≤ 2 := by
      have := (mem_compl.mp hxL)
      simp only [H, H3, mem_filter, mem_univ, true_and, not_le] at this
      omega
    have : A.filter (fun a => G.Adj a x) ⊆ G.neighborFinset x := by
      intro a ha
      rw [mem_neighborFinset]
      exact (mem_filter.mp ha).2.symm
    have := card_le_card this
    rw [card_neighborFinset_eq_degree] at this
    omega
  -- the edges from `A` to `C` are distinct edges of `G[H]`
  have h3 : ∑ a ∈ A, #(C.filter (G.Adj a)) ≤ edgesIn G H := by
    rw [← card_sigma]
    apply card_le_card_of_injOn (fun p => s(p.1, p.2))
    · intro p hp
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter] at hp
      obtain ⟨hpA, hpC, hadj⟩ := hp
      simp only [coe_filter, Set.mem_ofPred_eq, mem_edgeFinset, mem_edgeSet]
      refine ⟨hadj, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact (mem_inter.mp hpA).2
      · exact (mem_sdiff.mp hpC).1
    · intro p hp q hq hpq
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter] at hp hq
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      simp only at hpq hp hq
      rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        subst h2
        rfl
      · exact absurd (h1 ▸ (mem_inter.mp hp.1).1) (mem_sdiff.mp hq.2.1).2
  have hsum := sum_le_sum h1
  rw [sum_const, smul_eq_mul, sum_add_distrib] at hsum
  -- conclude
  have hS : #S = #A + #(S ∩ L) := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [A, L, mem_union, mem_inter, mem_compl]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx hx'
      exact (mem_compl.mp (mem_inter.mp hx').2) (mem_inter.mp hx).2
  have hL : #L = #B + #(S ∩ L) := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [B, mem_union, mem_sdiff, mem_inter]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx hx'
      exact (mem_sdiff.mp hx).2 (mem_inter.mp hx').1
  omega

/-- `⌈(e - 1)/2⌉ = ⌊e/2⌋` for every natural number `e`. -/
lemma ceil_eq (e : ℕ) : ⌈((e : ℝ) - 1) / 2⌉ = ((e / 2 : ℕ) : ℤ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' e
  · rw [show 2 * k / 2 = k by omega, Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith
  · rw [show (2 * k + 1) / 2 = k by omega, Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith

/-- **WOWII Conjecture 449.** For every finite graph,
`α_2(G) ≤ |V \ H_3| + ⌈(|E(G[H_3])| - 1)/2⌉`. -/
theorem conjecture449 (G : SimpleGraph V) :
    (twoIndepNum G : ℝ) ≤ #(H3 G)ᶜ + ⌈((edgesIn G (H3 G) : ℝ) - 1) / 2⌉ := by
  obtain ⟨S, hS, hcard⟩ := exists_twoIndep G
  have h := card_le G hS
  rw [hcard] at h
  rw [ceil_eq, Int.cast_natCast]
  exact_mod_cast h

end WOWII449
