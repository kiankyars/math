import Mathlib

/-!
# Subset sums of a skyline are vertically convex

A *skyline* is a finite set of lattice points `I ⊆ ℕ × ℕ` made of columns
`{a} × {0, …, h a - 1}` for `a = 0, …, K`, where every column is nonempty.
For a subset `S ⊆ I` write `S.sum Prod.fst` for its horizontal sum and
`S.sum Prod.snd` for its vertical sum.

**Theorem** (`Skyline.reach_interval`). For every horizontal sum `A`, the set of
vertical sums of subsets of `I` with horizontal sum `A` is an interval of
integers. The column heights are arbitrary, not necessarily monotone.

This is the two-prime case of Ang's conjecture on products of subsets of
`{1, …, n}` (OEIS A060957): see `OpenProblem.TwoPrimes`.

The proof adds one point at a time to the top of a column, keeping the invariant
`Inv`. Besides the interval property, `Inv` records that `T_A` meets
`T_{A-a} + (h a - 1)` for every column `a` (the `kl` field), and that the set of
reachable horizontal sums is the interval `[0, total]`.
-/

open Finset

namespace Skyline

/-- `Reach I A t`: some subset of `I` has horizontal sum `A` and vertical sum `t`. -/
def Reach (I : Finset (ℕ × ℕ)) (A t : ℕ) : Prop :=
  ∃ S ⊆ I, S.sum Prod.fst = A ∧ S.sum Prod.snd = t

/-- Subsets of `insert e I` either avoid `e` or contain it. -/
lemma reach_insert {I : Finset (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∉ I) (A t : ℕ) :
    Reach (insert e I) A t ↔
      Reach I A t ∨ (e.1 ≤ A ∧ e.2 ≤ t ∧ Reach I (A - e.1) (t - e.2)) := by
  constructor
  · rintro ⟨S, hS, hA, ht⟩
    by_cases heS : e ∈ S
    · right
      have hS' : S.erase e ⊆ I := by
        intro x hx
        rcases Finset.mem_insert.mp (hS (Finset.mem_of_mem_erase hx)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase hx)
        · exact h
      have h1 : (S.erase e).sum Prod.fst + e.1 = S.sum Prod.fst :=
        Finset.sum_erase_add S Prod.fst heS
      have h2 : (S.erase e).sum Prod.snd + e.2 = S.sum Prod.snd :=
        Finset.sum_erase_add S Prod.snd heS
      exact ⟨by omega, by omega, S.erase e, hS', by omega, by omega⟩
    · left
      refine ⟨S, ?_, hA, ht⟩
      intro x hx
      rcases Finset.mem_insert.mp (hS hx) with h | h
      · exact absurd (h ▸ hx) heS
      · exact h
  · rintro (⟨S, hS, hA, ht⟩ | ⟨h1, h2, S, hS, hA, ht⟩)
    · exact ⟨S, hS.trans (Finset.subset_insert _ _), hA, ht⟩
    · have heS : e ∉ S := fun h => he (hS h)
      refine ⟨insert e S, Finset.insert_subset_insert _ hS, ?_, ?_⟩
      · have : (insert e S).sum Prod.fst = e.1 + S.sum Prod.fst := Finset.sum_insert heS
        omega
      · have : (insert e S).sum Prod.snd = e.2 + S.sum Prod.snd := Finset.sum_insert heS
        omega

lemma Reach.mono {I J : Finset (ℕ × ℕ)} (hIJ : I ⊆ J) {A t : ℕ} (h : Reach I A t) :
    Reach J A t := by
  obtain ⟨S, hS, hA, ht⟩ := h
  exact ⟨S, hS.trans hIJ, hA, ht⟩

/-- The skyline with columns `0, …, K` of heights `h 0, …, h K`. -/
def sky (K : ℕ) (h : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (K + 1)).biUnion fun a => (Finset.range (h a)).image fun t => (a, t)

lemma mem_sky {K : ℕ} {h : ℕ → ℕ} {x : ℕ × ℕ} : x ∈ sky K h ↔ x.1 ≤ K ∧ x.2 < h x.1 := by
  obtain ⟨a, t⟩ := x
  simp only [sky, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨b, hb, s, hs, rfl, rfl⟩
    exact ⟨by omega, hs⟩
  · rintro ⟨ha, ht⟩
    exact ⟨a, by omega, t, ht, rfl, rfl⟩

/-- Total horizontal mass of the skyline. -/
def total (K : ℕ) (h : ℕ → ℕ) : ℕ := ∑ a ∈ Finset.range (K + 1), a * h a

/-- The point added when column `a₀` is raised by one. -/
lemma sky_update {K : ℕ} {h : ℕ → ℕ} {a₀ : ℕ} (ha₀ : a₀ ≤ K) :
    sky K (Function.update h a₀ (h a₀ + 1)) = insert (a₀, h a₀) (sky K h) := by
  ext ⟨a, t⟩
  simp only [mem_sky, Finset.mem_insert, Prod.mk.injEq]
  by_cases hab : a = a₀
  · subst hab
    rw [Function.update_self]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : t = h a
      · exact Or.inl ⟨rfl, h3⟩
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (⟨-, rfl⟩ | ⟨h1, h2⟩)
      · exact ⟨ha₀, by omega⟩
      · exact ⟨h1, by omega⟩
  · simp only [Function.update_of_ne hab]
    constructor
    · intro h; exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact absurd h1 hab
      · exact h

lemma not_mem_sky_top {K : ℕ} {h : ℕ → ℕ} (a₀ : ℕ) : (a₀, h a₀) ∉ sky K h := by
  simp [mem_sky]

lemma total_update {K : ℕ} {h : ℕ → ℕ} {a₀ : ℕ} (ha₀ : a₀ ≤ K) :
    total K (Function.update h a₀ (h a₀ + 1)) = total K h + a₀ := by
  unfold total
  have hmem : a₀ ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have : ∑ x ∈ (Finset.range (K + 1)).erase a₀, x * Function.update h a₀ (h a₀ + 1) x =
      ∑ x ∈ (Finset.range (K + 1)).erase a₀, x * h x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  ring

/-- Every subset of the skyline has horizontal sum at most `total`. -/
lemma sum_fst_le_total {K : ℕ} {h : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ sky K h) :
    S.sum Prod.fst ≤ total K h := by
  calc S.sum Prod.fst ≤ (sky K h).sum Prod.fst := Finset.sum_le_sum_of_subset hS
    _ = total K h := by
      unfold sky total
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_image]
        · simp [mul_comm]
        · intro x _ y _ hxy
          simpa using hxy
      · intro a _ b _ hab
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_image] at hx hx'
        obtain ⟨_, _, rfl⟩ := hx
        obtain ⟨_, _, hh⟩ := hx'
        exact hab (congrArg Prod.fst hh).symm

/-- Interval property of a predicate on `ℕ`. -/
def IsIvl (P : ℕ → Prop) : Prop :=
  ∀ t₁ t₂ t, P t₁ → P t₂ → t₁ ≤ t → t ≤ t₂ → P t

/-- The invariant carried through the induction. -/
structure Inv (K : ℕ) (h : ℕ → ℕ) : Prop where
  ivl : ∀ A, IsIvl (Reach (sky K h) A)
  kl : ∀ a ≤ K, ∀ A, a ≤ A → (∃ t, Reach (sky K h) A t) → (∃ s, Reach (sky K h) (A - a) s) →
    ∃ s, Reach (sky K h) (A - a) s ∧ Reach (sky K h) A (s + (h a - 1))
  rint : ∀ A, (∃ t, Reach (sky K h) A t) ↔ A ≤ total K h


lemma le_total_of_le {K : ℕ} {h : ℕ → ℕ} (hpos : ∀ a ≤ K, 1 ≤ h a) {a : ℕ} (ha : a ≤ K) :
    a ≤ total K h := by
  have hmem : a ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have h1 : a * h a ≤ total K h :=
    Finset.single_le_sum (f := fun x => x * h x) (fun _ _ => Nat.zero_le _) hmem
  have h2 : a ≤ a * h a := Nat.le_mul_of_pos_right a (hpos a ha)
  omega

lemma add_le_total {K : ℕ} {h : ℕ → ℕ} (hpos : ∀ a ≤ K, 1 ≤ h a) {a b : ℕ} (ha : a ≤ K)
    (hb : b ≤ K) (hab : a ≠ b) : a + b ≤ total K h := by
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.range (K + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have h1 := Finset.sum_le_sum_of_subset (f := fun x => x * h x) hsub
  rw [Finset.sum_pair hab] at h1
  have h2 : a ≤ a * h a := Nat.le_mul_of_pos_right a (hpos a ha)
  have h3 : b ≤ b * h b := Nat.le_mul_of_pos_right b (hpos b hb)
  unfold total
  omega

/-- Raising one column preserves the invariant. -/
theorem Inv.raise {K : ℕ} {h : ℕ → ℕ} (hI : Inv K h) (hpos : ∀ a ≤ K, 1 ≤ h a) {a₀ : ℕ}
    (ha₀ : a₀ ≤ K) : Inv K (Function.update h a₀ (h a₀ + 1)) := by
  set h' := Function.update h a₀ (h a₀ + 1) with hh'
  have hsky : sky K h' = insert (a₀, h a₀) (sky K h) := sky_update ha₀
  have hR : ∀ A t, Reach (sky K h') A t ↔
      Reach (sky K h) A t ∨ (a₀ ≤ A ∧ h a₀ ≤ t ∧ Reach (sky K h) (A - a₀) (t - h a₀)) := by
    intro A t
    rw [hsky]
    exact reach_insert (not_mem_sky_top a₀) A t
  have htot : total K h' = total K h + a₀ := total_update ha₀
  have hmono : ∀ A t, Reach (sky K h) A t → Reach (sky K h') A t :=
    fun A t hr => (hR A t).2 (Or.inl hr)
  have hup : ∀ A s, a₀ ≤ A → Reach (sky K h) (A - a₀) s → Reach (sky K h') A (s + h a₀) := by
    intro A s h1 h2
    apply (hR A (s + h a₀)).2
    right
    refine ⟨h1, by omega, ?_⟩
    rwa [Nat.add_sub_cancel]
  have hpa₀ : 1 ≤ h a₀ := hpos a₀ ha₀
  refine ⟨?_, ?_, ?_⟩
  · -- interval property
    intro A t₁ t₂ t ht₁ ht₂ h1 h2
    rcases (hR A t₁).1 ht₁ with r₁ | ⟨a₁, b₁, r₁⟩ <;>
      rcases (hR A t₂).1 ht₂ with r₂ | ⟨a₂, b₂, r₂⟩
    · exact hmono _ _ (hI.ivl A t₁ t₂ t r₁ r₂ h1 h2)
    · obtain ⟨s, hs₁, hs₂⟩ := hI.kl a₀ ha₀ A a₂ ⟨t₁, r₁⟩ ⟨_, r₂⟩
      by_cases hc : t ≤ s + (h a₀ - 1)
      · exact hmono _ _ (hI.ivl A t₁ (s + (h a₀ - 1)) t r₁ hs₂ h1 hc)
      · have hr : Reach (sky K h) (A - a₀) (t - h a₀) :=
          hI.ivl (A - a₀) s (t₂ - h a₀) (t - h a₀) hs₁ r₂ (by omega) (by omega)
        exact (hR A t).2 (Or.inr ⟨a₂, by omega, hr⟩)
    · obtain ⟨s, hs₁, hs₂⟩ := hI.kl a₀ ha₀ A a₁ ⟨t₂, r₂⟩ ⟨_, r₁⟩
      by_cases hc : s + (h a₀ - 1) ≤ t
      · exact hmono _ _ (hI.ivl A (s + (h a₀ - 1)) t₂ t hs₂ r₂ hc h2)
      · have hr : Reach (sky K h) (A - a₀) (t - h a₀) :=
          hI.ivl (A - a₀) (t₁ - h a₀) s (t - h a₀) r₁ hs₁ (by omega) (by omega)
        exact (hR A t).2 (Or.inr ⟨a₁, by omega, hr⟩)
    · have hr : Reach (sky K h) (A - a₀) (t - h a₀) :=
        hI.ivl (A - a₀) (t₁ - h a₀) (t₂ - h a₀) (t - h a₀) r₁ r₂ (by omega) (by omega)
      exact (hR A t).2 (Or.inr ⟨a₁, by omega, hr⟩)
  · -- the KL property
    rintro a ha A haA ⟨t, ht⟩ ⟨s₀, hs₀⟩
    have hRA : A ≤ total K h ∨ (a₀ ≤ A ∧ A - a₀ ≤ total K h) := by
      rcases (hR A t).1 ht with r | ⟨h1, _, r⟩
      · exact Or.inl ((hI.rint A).1 ⟨t, r⟩)
      · exact Or.inr ⟨h1, (hI.rint _).1 ⟨_, r⟩⟩
    have hRAa : A - a ≤ total K h ∨ (a₀ ≤ A - a ∧ A - a - a₀ ≤ total K h) := by
      rcases (hR (A - a) s₀).1 hs₀ with r | ⟨h1, _, r⟩
      · exact Or.inl ((hI.rint _).1 ⟨s₀, r⟩)
      · exact Or.inr ⟨h1, (hI.rint _).1 ⟨_, r⟩⟩
    by_cases hae : a = a₀
    · have hh'a : h' a = h a₀ + 1 := by rw [hae, hh', Function.update_self]
      rw [hh'a, Nat.add_sub_cancel]
      by_cases hr : ∃ s, Reach (sky K h) (A - a₀) s
      · obtain ⟨s, hs⟩ := hr
        refine ⟨s, hmono _ _ (by rw [hae]; exact hs), ?_⟩
        exact hup A s (by omega) hs
      · exfalso
        have hnr : ¬ (A - a₀ ≤ total K h) := fun hle => hr ((hI.rint _).2 hle)
        subst hae
        omega
    · have hh'a : h' a = h a := by rw [hh', Function.update_of_ne hae]
      rw [hh'a]
      by_cases c1 : (∃ t, Reach (sky K h) A t) ∧ (∃ s, Reach (sky K h) (A - a) s)
      · obtain ⟨s, hs₁, hs₂⟩ := hI.kl a ha A haA c1.1 c1.2
        exact ⟨s, hmono _ _ hs₁, hmono _ _ hs₂⟩
      by_cases c2 : a₀ ≤ A - a ∧ (∃ t, Reach (sky K h) (A - a₀) t) ∧
          (∃ s, Reach (sky K h) (A - a - a₀) s)
      · obtain ⟨hc, hA0, hAa0⟩ := c2
        have e1 : A - a₀ - a = A - a - a₀ := by omega
        obtain ⟨s, hs₁, hs₂⟩ := hI.kl a ha (A - a₀) (by omega) hA0 (by rw [e1]; exact hAa0)
        refine ⟨s + h a₀, hup (A - a) s hc (by rw [← e1]; exact hs₁), ?_⟩
        have := hup A (s + (h a - 1)) (by omega) hs₂
        rwa [show s + h a₀ + (h a - 1) = s + (h a - 1) + h a₀ by ring]
      · exfalso
        have nc1 : ¬ (A ≤ total K h ∧ A - a ≤ total K h) :=
          fun ⟨x, y⟩ => c1 ⟨(hI.rint A).2 x, (hI.rint _).2 y⟩
        have nc2 : ¬ (a₀ ≤ A - a ∧ A - a₀ ≤ total K h ∧ A - a - a₀ ≤ total K h) :=
          fun ⟨x, y, z⟩ => c2 ⟨x, (hI.rint _).2 y, (hI.rint _).2 z⟩
        have h2 := add_le_total hpos ha ha₀ hae
        omega
  · -- reachable horizontal sums
    intro A
    rw [htot]
    constructor
    · rintro ⟨t, ht⟩
      rcases (hR A t).1 ht with r | ⟨h1, _, r⟩
      · have := (hI.rint A).1 ⟨t, r⟩; omega
      · have := (hI.rint _).1 ⟨_, r⟩; omega
    · intro hA
      by_cases hle : A ≤ total K h
      · obtain ⟨t, ht⟩ := (hI.rint A).2 hle
        exact ⟨t, hmono _ _ ht⟩
      · have ha0le : a₀ ≤ A := by have := le_total_of_le hpos ha₀; omega
        obtain ⟨s, hs⟩ := (hI.rint (A - a₀)).2 (by omega)
        exact ⟨_, hup A s ha0le hs⟩

/-- Subset sums of `{0, …, K}` fill the interval `[0, K(K+1)/2]`. -/
lemma exists_subset_sum (K : ℕ) : ∀ A, A ≤ ∑ a ∈ Finset.range (K + 1), a →
    ∃ T ⊆ Finset.range (K + 1), T.sum id = A := by
  induction K with
  | zero =>
    intro A hA
    simp at hA
    exact ⟨∅, Finset.empty_subset _, by simp [hA]⟩
  | succ K ih =>
    intro A hA
    rw [Finset.sum_range_succ] at hA
    by_cases hle : A ≤ ∑ a ∈ Finset.range (K + 1), a
    · obtain ⟨T, hT, hs⟩ := ih A hle
      refine ⟨T, fun x hx => ?_, hs⟩
      have := Finset.mem_range.mp (hT hx)
      exact Finset.mem_range.mpr (by omega)
    · have hK : K ≤ ∑ a ∈ Finset.range (K + 1), a :=
        Finset.single_le_sum (f := fun a => a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
      obtain ⟨T, hT, hs⟩ := ih (A - (K + 1)) (by omega)
      have hnot : K + 1 ∉ T := fun h => by simpa using hT h
      refine ⟨insert (K + 1) T, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hT hx); omega)
      · rw [Finset.sum_insert hnot, hs]
        simp only [id]
        omega

/-- The base case: all columns have height one. -/
theorem inv_base {K : ℕ} {h : ℕ → ℕ} (h1 : ∀ a ≤ K, h a = 1) : Inv K h := by
  have hsnd : ∀ S ⊆ sky K h, S.sum Prod.snd = 0 := by
    intro S hS
    apply Finset.sum_eq_zero
    intro x hx
    have := mem_sky.mp (hS hx)
    rw [h1 x.1 this.1] at this
    omega
  have htot : total K h = ∑ a ∈ Finset.range (K + 1), a := by
    unfold total
    apply Finset.sum_congr rfl
    intro a ha
    rw [h1 a (by simpa [Nat.lt_succ_iff] using ha), mul_one]
  have hreach : ∀ A t, Reach (sky K h) A t ↔ t = 0 ∧ A ≤ total K h := by
    intro A t
    constructor
    · rintro ⟨S, hS, hA, ht⟩
      exact ⟨by rw [← ht, hsnd S hS], hA ▸ sum_fst_le_total hS⟩
    · rintro ⟨rfl, hA⟩
      rw [htot] at hA
      obtain ⟨T, hT, hs⟩ := exists_subset_sum K A hA
      refine ⟨T.image fun a => (a, 0), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        have haK : a ≤ K := by have := Finset.mem_range.mp (hT ha); omega
        exact mem_sky.mpr ⟨haK, by rw [h1 a haK]; omega⟩
      · rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy)]
        simpa using hs
      · rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy)]
        simp
  refine ⟨?_, ?_, ?_⟩
  · intro A t₁ t₂ t ht₁ ht₂ ha hb
    rw [hreach] at ht₁ ht₂ ⊢
    exact ⟨by omega, ht₁.2⟩
  · rintro a ha A _ ⟨t, ht⟩ ⟨s, hs⟩
    rw [hreach] at ht hs
    refine ⟨0, (hreach _ _).2 ⟨rfl, hs.2⟩, (hreach _ _).2 ⟨by rw [h1 a ha], ht.2⟩⟩
  · intro A
    constructor
    · rintro ⟨t, ht⟩
      exact ((hreach A t).1 ht).2
    · intro hA
      exact ⟨0, (hreach A 0).2 ⟨rfl, hA⟩⟩

/-- The invariant holds for every skyline whose columns `0, …, K` are nonempty. -/
theorem inv_of_pos (K : ℕ) : ∀ (n : ℕ) (h : ℕ → ℕ),
    ∑ a ∈ Finset.range (K + 1), (h a - 1) = n → (∀ a ≤ K, 1 ≤ h a) → Inv K h := by
  intro n
  induction n with
  | zero =>
    intro h hn hpos
    apply inv_base
    intro a ha
    have hmem : a ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    have := (Finset.sum_eq_zero_iff.mp hn) a hmem
    have := hpos a ha
    omega
  | succ n ih =>
    intro h hn hpos
    obtain ⟨a₀, ha₀, h2⟩ : ∃ a₀ ≤ K, 2 ≤ h a₀ := by
      by_contra hc
      push Not at hc
      have : ∑ a ∈ Finset.range (K + 1), (h a - 1) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have := hc a (by simpa [Nat.lt_succ_iff] using ha)
        omega
      omega
    set g := Function.update h a₀ (h a₀ - 1) with hg
    have hga₀ : g a₀ = h a₀ - 1 := by rw [hg, Function.update_self]
    have hgh : Function.update g a₀ (g a₀ + 1) = h := by
      rw [hga₀, hg, Function.update_idem, show h a₀ - 1 + 1 = h a₀ by omega,
        Function.update_eq_self]
    have hgpos : ∀ a ≤ K, 1 ≤ g a := by
      intro a ha
      by_cases hae : a = a₀
      · rw [hae, hga₀]; omega
      · rw [hg, Function.update_of_ne hae]; exact hpos a ha
    have hgn : ∑ a ∈ Finset.range (K + 1), (g a - 1) = n := by
      have hmem : a₀ ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hmem] at hn ⊢
      have : ∑ x ∈ (Finset.range (K + 1)).erase a₀, (g x - 1) =
          ∑ x ∈ (Finset.range (K + 1)).erase a₀, (h x - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hg, Function.update_of_ne (Finset.ne_of_mem_erase hx)]
      rw [this, hga₀]
      omega
    have := (ih g hgn hgpos).raise hgpos ha₀
    rwa [hgh] at this

/-- **Main theorem.** For a skyline whose columns `0, …, K` are all nonempty, the vertical
sums of subsets with a fixed horizontal sum form an interval. -/
theorem reach_interval {K : ℕ} {h : ℕ → ℕ} (hpos : ∀ a ≤ K, 1 ≤ h a) (A : ℕ) :
    IsIvl (Reach (sky K h) A) :=
  (inv_of_pos K _ h rfl hpos).ivl A

end Skyline
