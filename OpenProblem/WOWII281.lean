import OpenProblem.WOWII300
import OpenProblem.WOWII326

/-!
# Written on the Wall II, Conjecture 281 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 281.** If `G` is a simple connected graph such that `n(G) > 2`, then
> `γ_t(G) ≤ [frequency of λ_min(Ḡ)] + μ(G)`.

Here `λ_Ḡ(v) = α(Ḡ[N_Ḡ(v)])` is the order of a largest clique of `G` among the non-neighbours
of `v`, and `μ` is the matching number.

The counterexample `G13` has 13 vertices:

* a `K_4` on `3, 5, 7, 10` and a triangle `0, 1, 9`, with `0` and `1` adjacent to `5`;
* the paths `2 - 10`, `4 - 7` and `11 - 3`, with leaves `12` at `2`, `8` at `4` and `6` at `11`.

Only `N[5]` meets both the triangle `0, 1, 9` and the triangle `3, 7, 10`. So `λ_Ḡ(5) ≤ 2`
while `λ_Ḡ(v) ≥ 3` for every other `v`, and the frequency is `1`. Since `n = 13` is odd,
`μ ≤ 6`, so the bound is at most `7`.

But `γ_t(G13) = 8`. A total dominating set contains the supports `2`, `4` and `11`, a neighbour
of each of them, and two vertices among `0, 1, 5, 9`: a neighbour `u ∈ {0, 1}` of `9` and a
neighbour of `u`. These groups are disjoint.

All connected graphs with at most 9 vertices satisfy the conjecture. Simulated annealing finds
counterexamples with 13 vertices and none with 10, 11 or 12.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII281

open SimpleGraph WOWII178 WOWII372 WOWII326 WOWII300

variable {V : Type*} [Fintype V]

/-- A matching covers `2 μ` distinct vertices. -/
lemma two_mul_card_le {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M) :
    2 * #M ≤ Fintype.card V := by
  have h1 : ∀ e ∈ M, #(univ.filter fun v => v ∈ e) = 2 := by
    intro e he
    have heG := hM.1 he
    rw [mem_edgeFinset] at heG
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := G.ne_of_adj heG
      rw [show (univ.filter fun v => v ∈ s(a, b)) = {a, b} by ext; simp [Sym2.mem_iff]]
      exact card_pair hab
  have h2 : ∀ v, #(M.filter fun e => v ∈ e) ≤ 1 := by
    intro v
    rw [card_le_one]
    intro e he f hf
    by_contra hef
    exact hM.2 e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hef v (mem_filter.mp he).2
      (mem_filter.mp hf).2
  have hsum : ∑ e ∈ M, #(univ.filter fun v => v ∈ e) = ∑ v, #(M.filter fun e => v ∈ e) := by
    simp_rw [card_eq_sum_ones, sum_filter]
    exact sum_comm
  have h3 : ∑ v, #(M.filter fun e => v ∈ e) ≤ ∑ _v : V, 1 := sum_le_sum fun v _ => h2 v
  rw [sum_congr rfl h1, sum_const, smul_eq_mul] at hsum
  rw [sum_const, card_univ, smul_eq_mul, mul_one] at h3
  omega

/-- The statement of Conjecture 281. -/
def Conjecture281 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    totalDomNum G ≤ freqMinLocalIndep Gᶜ + matchingNumber G

/-! ### The counterexample -/

/-- The edges of `G13`. -/
def E13 : List (Fin 13 × Fin 13) :=
  [(0, 1), (0, 5), (0, 9), (1, 5), (1, 9), (3, 5), (3, 7), (3, 10), (5, 7), (5, 10), (7, 10),
    (2, 10), (2, 12), (4, 7), (4, 8), (3, 11), (6, 11)]

def adj13 (a b : Fin 13) : Bool := E13.contains (a, b) || E13.contains (b, a)

/-- A `K_4` and a triangle sharing the neighbour `5`, with three pendant paths. -/
def G13 : SimpleGraph (Fin 13) := SimpleGraph.fromRel fun a b => adj13 a b = true

lemma G13_adj {a b : Fin 13} : G13.Adj a b ↔ adj13 a b = true := by
  have h : ∀ a b : Fin 13, (a ≠ b ∧ (adj13 a b = true ∨ adj13 b a = true)) ↔
      adj13 a b = true := by decide
  simpa [G13] using h a b

/-- A neighbour closer to `5`, and the distance from `5`. -/
def par13 : Fin 13 → Fin 13 := ![5, 5, 10, 5, 7, 5, 11, 5, 4, 0, 5, 3, 2]
def d13 : Fin 13 → ℕ := ![1, 1, 2, 1, 2, 0, 3, 1, 3, 2, 1, 2, 3]

lemma G13_connected : G13.Connected := by
  refine WOWII267.connected_of_parent 5 d13 par13 fun v hv => ?_
  rw [G13_adj]
  revert v
  decide

/-- Every total dominating set of `G13` has at least eight vertices. -/
lemma card_ge_of_isTDS {S : Finset (Fin 13)} (hS : IsTDS G13 S) : 8 ≤ #S := by
  have hN : ∀ v, ∃ u ∈ S, adj13 v u = true := fun v => by
    obtain ⟨u, hu, h⟩ := hS v
    exact ⟨u, hu, G13_adj.mp h⟩
  -- the supports of the leaves
  have h2 : (2 : Fin 13) ∈ S := by
    obtain ⟨u, hu, h⟩ := hN 12
    have : ∀ u : Fin 13, adj13 12 u = true → u = 2 := by decide
    rwa [← this u h]
  have h4 : (4 : Fin 13) ∈ S := by
    obtain ⟨u, hu, h⟩ := hN 8
    have : ∀ u : Fin 13, adj13 8 u = true → u = 4 := by decide
    rwa [← this u h]
  have h11 : (11 : Fin 13) ∈ S := by
    obtain ⟨u, hu, h⟩ := hN 6
    have : ∀ u : Fin 13, adj13 6 u = true → u = 11 := by decide
    rwa [← this u h]
  -- their neighbours
  obtain ⟨a, ha, ha'⟩ := hN 2
  obtain ⟨b, hb, hb'⟩ := hN 4
  obtain ⟨c, hc, hc'⟩ := hN 11
  -- a neighbour `u` of `9` and a neighbour `w` of `u`
  obtain ⟨u, hu, hu'⟩ := hN 9
  obtain ⟨w, hw, hw'⟩ := hN u
  have hA : a ∈ ({10, 12} : Finset (Fin 13)) :=
    (by decide : ∀ a : Fin 13, adj13 2 a = true → a ∈ ({10, 12} : Finset (Fin 13))) a ha'
  have hB : b ∈ ({7, 8} : Finset (Fin 13)) :=
    (by decide : ∀ b : Fin 13, adj13 4 b = true → b ∈ ({7, 8} : Finset (Fin 13))) b hb'
  have hC : c ∈ ({3, 6} : Finset (Fin 13)) :=
    (by decide : ∀ c : Fin 13, adj13 11 c = true → c ∈ ({3, 6} : Finset (Fin 13))) c hc'
  have hU : u ∈ ({0, 1} : Finset (Fin 13)) :=
    (by decide : ∀ u : Fin 13, adj13 9 u = true → u ∈ ({0, 1} : Finset (Fin 13))) u hu'
  have hW : w ∈ ({0, 1, 5, 9} : Finset (Fin 13)) ∧ w ≠ u := by
    have : ∀ u ∈ ({0, 1} : Finset (Fin 13)), ∀ w : Fin 13, adj13 u w = true →
        w ∈ ({0, 1, 5, 9} : Finset (Fin 13)) ∧ w ≠ u := by decide
    exact this u hU w hw'
  have hcount : ∀ a ∈ ({10, 12} : Finset (Fin 13)), ∀ b ∈ ({7, 8} : Finset (Fin 13)),
      ∀ c ∈ ({3, 6} : Finset (Fin 13)), ∀ u ∈ ({0, 1} : Finset (Fin 13)),
      ∀ w ∈ ({0, 1, 5, 9} : Finset (Fin 13)), w ≠ u →
      #({2, 4, 11, a, b, c, u, w} : Finset (Fin 13)) = 8 := by decide
  rw [← hcount a hA b hB c hC u hU w hW.1 hW.2]
  apply card_le_card
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

lemma G13_totalDomNum : 8 ≤ totalDomNum G13 := by
  obtain ⟨S, hS, hcard⟩ := exists_tds_card_eq (G := G13) fun v => by
    have : ∀ v : Fin 13, ∃ u, adj13 v u = true := by decide
    obtain ⟨u, hu⟩ := this v
    exact ⟨u, G13_adj.mpr hu⟩
  rw [← hcard]
  exact card_ge_of_isTDS hS

lemma G13_matchingNumber : matchingNumber G13 ≤ 6 := by
  obtain ⟨M, hM, hcard⟩ := exists_max_matching G13
  have := two_mul_card_le hM
  rw [Fintype.card_fin] at this
  omega

/-- A triangle of `G13` avoiding `N[v]`, for `v ≠ 5`. -/
def tri (v : Fin 13) : Finset (Fin 13) :=
  if v = 0 ∨ v = 1 ∨ v = 9 then {3, 7, 10} else {0, 1, 9}

lemma three_le_localIndep (v : Fin 13) (hv : v ≠ 5) : 3 ≤ localIndep G13ᶜ v := by
  have h : ∀ v : Fin 13, v ≠ 5 → (∀ x ∈ tri v, x ≠ v ∧ adj13 v x = false) ∧
      (∀ x ∈ tri v, ∀ y ∈ tri v, x = y ∨ adj13 x y = true) ∧ #(tri v) = 3 := by decide
  obtain ⟨h1, h2, h3⟩ := h v hv
  rw [← h3]
  apply WOWII96.card_le_localIndep
  · intro x hx
    obtain ⟨hxv, hadj⟩ := h1 x hx
    rw [compl_adj, G13_adj, hadj]
    exact ⟨hxv.symm, Bool.false_ne_true⟩
  · intro x hx y hy hxy
    rw [compl_adj, G13_adj] at hxy
    rcases h2 x hx y hy with h | h
    · exact hxy.1 h
    · exact hxy.2 h

lemma localIndep_five_le : localIndep G13ᶜ 5 ≤ 2 := by
  obtain ⟨I, hI5, hII, hcard⟩ := exists_indep_nbhd G13ᶜ 5
  rw [← hcard]
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hlt
  have hG : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → adj13 x y = true := by
    intro x hx y hy hxy
    by_contra h
    exact hII x hx y hy ((compl_adj G13 x y).mpr ⟨hxy, fun h' => h (G13_adj.mp h')⟩)
  have h5 : ∀ x ∈ I, adj13 5 x = false ∧ x ≠ 5 := by
    intro x hx
    obtain ⟨hne, hadj⟩ := (compl_adj G13 5 x).mp (hI5 x hx)
    refine ⟨?_, hne.symm⟩
    by_contra h
    exact hadj (G13_adj.mpr (by simpa using h))
  have key : ∀ a b c : Fin 13, adj13 a b = true → adj13 a c = true → adj13 b c = true →
      adj13 5 a = false → adj13 5 b = false → adj13 5 c = false → a = 5 ∨ b = 5 ∨ c = 5 := by
    decide
  rcases key a b c (hG a ha b hb hab) (hG a ha c hc hac) (hG b hb c hc hbc) (h5 a ha).1
    (h5 b hb).1 (h5 c hc).1 with h | h | h
  · exact (h5 a ha).2 h
  · exact (h5 b hb).2 h
  · exact (h5 c hc).2 h

lemma G13_freq : freqMinLocalIndep G13ᶜ = 1 := by
  have hmin : WOWII162.minLocalIndep G13ᶜ = localIndep G13ᶜ 5 := by
    apply le_antisymm (Nat.sInf_le (Set.mem_range_self 5))
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨v, rfl⟩
    by_cases hv : v = 5
    · rw [hv]
    · have := three_le_localIndep v hv
      have := localIndep_five_le
      omega
  rw [freqMinLocalIndep, hmin, card_eq_one]
  refine ⟨5, ?_⟩
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    by_contra hv
    have := three_le_localIndep v hv
    have := localIndep_five_le
    omega
  · rintro rfl
    rfl

/-- **WOWII Conjecture 281 is false.** -/
theorem not_conjecture281 : ¬ Conjecture281 := by
  intro h
  have h1 := h (Fin 13) G13 G13_connected (by simp)
  rw [G13_freq] at h1
  have := G13_totalDomNum
  have := G13_matchingNumber
  omega

end WOWII281
