import OpenProblem.WOWII162
import OpenProblem.WOWII267

/-!
# Written on the Wall II, Conjecture 300 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 300.** If `G` is a simple connected graph such that `n(G) > 2`, then
> `γ_t(G) ≤ (1/2)*[n(G) + frequency of λ_min(Ḡ)]`.

Here `λ(v) = α(G[N(v)])` computed in the complement `Ḡ`, so `λ_Ḡ(v)` is the order of a largest
clique of `G` among the vertices not adjacent to `v`. The frequency of `λ_min(Ḡ)` is the number
of vertices at which `λ_Ḡ` is minimal.

The counterexample `G12` has 12 vertices and is made of:

* a triangle `0, 1, 2` and a triangle `7, 8, 9`, joined by the path `2 - 5 - 7`;
* a leaf `4` at `0`, the path `2 - 10 - 3`, and the path `1 - 11 - 6`.

Only `N[5]` meets both triangles, so `λ_Ḡ(5) ≤ 2` while `λ_Ḡ(v) ≥ 3` for every other vertex `v`.
Hence the frequency is `1` and the bound is `13/2`.

But `γ_t(G12) = 7`. A total dominating set contains `0`, `10` and `11`, the supports of the
leaves. It meets `N(10) = {2, 3}` and `N(11) = {1, 6}`, and it has at least two vertices among
`5, 7, 8, 9` to dominate the triangle `7, 8, 9`. These groups are disjoint.

All connected graphs with at most 9 vertices satisfy the conjecture. Simulated annealing finds
many counterexamples with 12 vertices and none with 10 or 11.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII300

open SimpleGraph WOWII178 WOWII372

variable {V : Type*} [Fintype V]

/-- The number of vertices at which `λ` is minimal. -/
def freqMinLocalIndep (G : SimpleGraph V) : ℕ :=
  #(univ.filter fun v => localIndep G v = WOWII162.minLocalIndep G)

/-- The statement of Conjecture 300. -/
def Conjecture300 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    (totalDomNum G : ℝ) ≤ (Fintype.card V + freqMinLocalIndep Gᶜ) / 2

/-! ### The counterexample -/

/-- The edges of `G12`. -/
def E12 : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 2), (1, 2), (0, 4), (1, 11), (11, 6), (2, 10), (10, 3), (2, 5), (5, 7),
    (7, 8), (7, 9), (8, 9)]

def adj12 (a b : Fin 12) : Bool := E12.contains (a, b) || E12.contains (b, a)

/-- Two triangles joined by a path of length two, with three pendant paths. -/
def G12 : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adj12 a b = true

lemma G12_adj {a b : Fin 12} : G12.Adj a b ↔ adj12 a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adj12 a b = true ∨ adj12 b a = true)) ↔
      adj12 a b = true := by decide
  simpa [G12] using h a b

/-- A neighbour closer to `0`, and the distance from `0`. -/
def par12 : Fin 12 → Fin 12 := ![0, 0, 0, 10, 0, 2, 11, 5, 7, 7, 2, 1]
def d12 : Fin 12 → ℕ := ![0, 1, 1, 3, 1, 2, 3, 3, 4, 4, 2, 2]

lemma G12_connected : G12.Connected := by
  refine WOWII267.connected_of_parent 0 d12 par12 fun v hv => ?_
  rw [G12_adj]
  revert v
  decide

/-- Every total dominating set of `G12` has at least seven vertices. -/
lemma card_ge_of_isTDS {S : Finset (Fin 12)} (hS : IsTDS G12 S) : 7 ≤ #S := by
  have hN : ∀ v, ∃ u ∈ S, adj12 v u = true := fun v => by
    obtain ⟨u, hu, h⟩ := hS v
    exact ⟨u, hu, G12_adj.mp h⟩
  -- the supports of the leaves
  have h0 : (0 : Fin 12) ∈ S := by
    obtain ⟨u, hu, h⟩ := hN 4
    have : ∀ u : Fin 12, adj12 4 u = true → u = 0 := by decide
    rwa [← this u h]
  have h10 : (10 : Fin 12) ∈ S := by
    obtain ⟨u, hu, h⟩ := hN 3
    have : ∀ u : Fin 12, adj12 3 u = true → u = 10 := by decide
    rwa [← this u h]
  have h11 : (11 : Fin 12) ∈ S := by
    obtain ⟨u, hu, h⟩ := hN 6
    have : ∀ u : Fin 12, adj12 6 u = true → u = 11 := by decide
    rwa [← this u h]
  -- the neighbourhoods of `10` and `11`
  obtain ⟨a, ha, ha'⟩ := hN 10
  obtain ⟨b, hb, hb'⟩ := hN 11
  -- two vertices among `5, 7, 8, 9`
  obtain ⟨c, hc, d, hd, hcd, hcd'⟩ : ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      (adj12 8 c = true ∨ adj12 9 c = true ∨ adj12 7 c = true ∨ c = 7) ∧
      (adj12 8 d = true ∨ adj12 9 d = true ∨ adj12 7 d = true ∨ d = 7) := by
    obtain ⟨u, hu, h8⟩ := hN 8
    obtain ⟨u', hu', h9⟩ := hN 9
    by_cases huu : u = u'
    · subst huu
      have h7 : u = 7 := by
        have : ∀ u : Fin 12, adj12 8 u = true → adj12 9 u = true → u = 7 := by decide
        exact this u h8 h9
      subst h7
      obtain ⟨w, hw, h7w⟩ := hN 7
      refine ⟨7, hu, w, hw, ?_, Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inr (Or.inl h7w))⟩
      rintro rfl
      exact absurd h7w (by decide)
    · exact ⟨u, hu, u', hu', huu, Or.inl h8, Or.inr (Or.inl h9)⟩
  have hcount : ∀ a b c d : Fin 12, adj12 10 a = true → adj12 11 b = true → c ≠ d →
      (adj12 8 c = true ∨ adj12 9 c = true ∨ adj12 7 c = true ∨ c = 7) →
      (adj12 8 d = true ∨ adj12 9 d = true ∨ adj12 7 d = true ∨ d = 7) →
      #({0, 10, 11, a, b, c, d} : Finset (Fin 12)) = 7 := by decide
  rw [← hcount a b c d ha' hb' hcd hcd'.1 hcd'.2]
  apply card_le_card
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

lemma G12_totalDomNum : 7 ≤ totalDomNum G12 := by
  obtain ⟨S, hS, hcard⟩ := exists_tds_card_eq (G := G12) fun v => by
    have : ∀ v : Fin 12, ∃ u, adj12 v u = true := by decide
    obtain ⟨u, hu⟩ := this v
    exact ⟨u, G12_adj.mpr hu⟩
  rw [← hcard]
  exact card_ge_of_isTDS hS

/-- The triangle of `G12` avoiding `N[v]`, for `v ≠ 5`. -/
def tri (v : Fin 12) : Finset (Fin 12) := if v.val ≤ 6 ∨ 10 ≤ v.val then {7, 8, 9} else {0, 1, 2}

lemma three_le_localIndep (v : Fin 12) (hv : v ≠ 5) : 3 ≤ localIndep G12ᶜ v := by
  have h : ∀ v : Fin 12, v ≠ 5 → (∀ x ∈ tri v, x ≠ v ∧ adj12 v x = false) ∧
      (∀ x ∈ tri v, ∀ y ∈ tri v, x = y ∨ adj12 x y = true) ∧ #(tri v) = 3 := by decide
  obtain ⟨h1, h2, h3⟩ := h v hv
  rw [← h3]
  apply WOWII96.card_le_localIndep
  · intro x hx
    obtain ⟨hxv, hadj⟩ := h1 x hx
    rw [compl_adj, G12_adj, hadj]
    exact ⟨hxv.symm, Bool.false_ne_true⟩
  · intro x hx y hy hxy
    rw [compl_adj, G12_adj] at hxy
    rcases h2 x hx y hy with h | h
    · exact hxy.1 h
    · exact hxy.2 h

lemma localIndep_five_le : localIndep G12ᶜ 5 ≤ 2 := by
  obtain ⟨I, hI5, hII, hcard⟩ := exists_indep_nbhd G12ᶜ 5
  rw [← hcard]
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hlt
  have hG : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → adj12 x y = true := by
    intro x hx y hy hxy
    by_contra h
    exact hII x hx y hy ((compl_adj G12 x y).mpr ⟨hxy, fun h' => h (G12_adj.mp h')⟩)
  have h5 : ∀ x ∈ I, adj12 5 x = false ∧ x ≠ 5 := by
    intro x hx
    obtain ⟨hne, hadj⟩ := (compl_adj G12 5 x).mp (hI5 x hx)
    refine ⟨?_, hne.symm⟩
    by_contra h
    exact hadj (G12_adj.mpr (by simpa using h))
  have key : ∀ a b c : Fin 12, adj12 a b = true → adj12 a c = true → adj12 b c = true →
      adj12 5 a = false → adj12 5 b = false → adj12 5 c = false → a = 5 ∨ b = 5 ∨ c = 5 := by
    decide
  rcases key a b c (hG a ha b hb hab) (hG a ha c hc hac) (hG b hb c hc hbc) (h5 a ha).1
    (h5 b hb).1 (h5 c hc).1 with h | h | h
  · exact (h5 a ha).2 h
  · exact (h5 b hb).2 h
  · exact (h5 c hc).2 h

lemma G12_freq : freqMinLocalIndep G12ᶜ = 1 := by
  have hmin : WOWII162.minLocalIndep G12ᶜ = localIndep G12ᶜ 5 := by
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

/-- **WOWII Conjecture 300 is false.** -/
theorem not_conjecture300 : ¬ Conjecture300 := by
  intro h
  have h1 := h (Fin 12) G12 G12_connected (by simp)
  rw [G12_freq, Fintype.card_fin] at h1
  have h2 : (7 : ℝ) ≤ totalDomNum G12 := by exact_mod_cast G12_totalDomNum
  norm_num at h1
  linarith

end WOWII300
