import OpenProblem.Skyline

/-!
# Ang's conjecture for products of `{p, q}`-smooth numbers

Ang's conjecture (OEIS A060957) states that if `m` and `p ^ e * m` are both products of
subsets of `{1, …, n}`, then so is `p ^ k * m` for every `k ≤ e`. It is open in general.

Here we prove the analogous statement when `{1, …, n}` is replaced by the set of
`{p, q}`-smooth numbers in `[1, n]`, for two distinct primes `p` and `q`. The proof
identifies these numbers with a skyline in `ℕ × ℕ` via `q ^ a * p ^ t ↦ (a, t)` and applies
`Skyline.reach_interval`.
-/

open Finset

namespace TwoPrimes

/-- The exponent pairs `(a, t)` with `q ^ a * p ^ t ≤ n`. -/
def expPairs (p q n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun x => q ^ x.1 * p ^ x.2 ≤ n

/-- The map `(a, t) ↦ q ^ a * p ^ t`. -/
def toNat (p q : ℕ) (x : ℕ × ℕ) : ℕ := q ^ x.1 * p ^ x.2

/-- The `{p, q}`-smooth numbers in `[1, n]`. -/
def smooth (p q n : ℕ) : Finset ℕ := (expPairs p q n).image (toNat p q)

lemma factorization_toNat_left {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (x : ℕ × ℕ) : (toNat p q x).factorization q = x.1 := by
  unfold toNat
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hq.factorization, hp.factorization, hpq]

lemma factorization_toNat_right {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (x : ℕ × ℕ) : (toNat p q x).factorization p = x.2 := by
  unfold toNat
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hq.factorization, hp.factorization, Ne.symm hpq]

lemma toNat_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (toNat p q) := by
  intro x y hxy
  have h1 := factorization_toNat_left hp hq hpq x
  have h2 := factorization_toNat_right hp hq hpq x
  rw [hxy, factorization_toNat_left hp hq hpq] at h1
  rw [hxy, factorization_toNat_right hp hq hpq] at h2
  exact Prod.ext h1.symm h2.symm

/-- Membership in `smooth`: exactly the numbers `q ^ a * p ^ t ≤ n`. -/
lemma mem_smooth {p q n x : ℕ} (hp : p.Prime) (hq : q.Prime) :
    x ∈ smooth p q n ↔ x ≤ n ∧ ∃ a t, x = q ^ a * p ^ t := by
  unfold smooth expPairs toNat
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨a, t⟩, ⟨_, hle⟩, rfl⟩
    exact ⟨hle, a, t, rfl⟩
  · rintro ⟨hle, a, t, rfl⟩
    have ha : a < q ^ a := Nat.lt_pow_self hq.one_lt
    have ht : t < p ^ t := Nat.lt_pow_self hp.one_lt
    have h1 : q ^ a ≤ q ^ a * p ^ t := Nat.le_mul_of_pos_right _ (pow_pos hp.pos _)
    have h2 : p ^ t ≤ q ^ a * p ^ t := Nat.le_mul_of_pos_left _ (pow_pos hq.pos _)
    exact ⟨(a, t), ⟨⟨by omega, by omega⟩, hle⟩, rfl⟩

/-- For `n ≥ 1` the exponent pairs form the skyline with `K = log_q n` and column heights
`log_p (n / q ^ a) + 1`. -/
lemma expPairs_eq_sky {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hn : 1 ≤ n) :
    expPairs p q n = Skyline.sky (Nat.log q n) (fun a => Nat.log p (n / q ^ a) + 1) := by
  ext ⟨a, t⟩
  rw [Skyline.mem_sky]
  unfold expPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  have hqa : 0 < q ^ a := pow_pos hq.pos _
  constructor
  · rintro ⟨_, hle⟩
    have h1 : q ^ a ≤ n := le_trans (Nat.le_mul_of_pos_right _ (pow_pos hp.pos _)) hle
    have hdiv : 1 ≤ n / q ^ a := (Nat.le_div_iff_mul_le hqa).mpr (by simpa using h1)
    refine ⟨(Nat.le_log_iff_pow_le hq.one_lt (by omega)).mpr h1, ?_⟩
    have h2 : p ^ t ≤ n / q ^ a := (Nat.le_div_iff_mul_le hqa).mpr (by rw [mul_comm]; exact hle)
    have := (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mpr h2
    omega
  · rintro ⟨ha, ht⟩
    have h1 : q ^ a ≤ n := (Nat.le_log_iff_pow_le hq.one_lt (by omega)).mp ha
    have hdiv : 1 ≤ n / q ^ a := (Nat.le_div_iff_mul_le hqa).mpr (by simpa using h1)
    have ht' : t ≤ Nat.log p (n / q ^ a) := by omega
    have h2 : p ^ t ≤ n / q ^ a := (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mp ht'
    have hle : q ^ a * p ^ t ≤ n := by
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le hqa).mp h2
    have ha' : a < q ^ a := Nat.lt_pow_self hq.one_lt
    have ht'' : t < p ^ t := Nat.lt_pow_self hp.one_lt
    have h3 : p ^ t ≤ q ^ a * p ^ t := Nat.le_mul_of_pos_left _ hqa
    exact ⟨⟨by omega, by omega⟩, hle⟩

/-- The product of the image of `S` is `q ^ (Σ a) * p ^ (Σ t)`. -/
lemma prod_image_toNat {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (S : Finset (ℕ × ℕ)) :
    (S.image (toNat p q)).prod id = q ^ S.sum Prod.fst * p ^ S.sum Prod.snd := by
  rw [Finset.prod_image (fun x _ y _ hxy => toNat_injective hp hq hpq hxy)]
  simp only [id, toNat]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

/-- Products of subsets of `smooth p q n` are exactly the numbers `q ^ A * p ^ t` with
`Reach (expPairs p q n) A t`. -/
lemma prod_iff {p q n m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (∃ s ⊆ smooth p q n, s.prod id = m) ↔
      ∃ A t, Skyline.Reach (expPairs p q n) A t ∧ m = q ^ A * p ^ t := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨S, hS, rfl⟩ := Finset.subset_image_iff.mp hs
    exact ⟨_, _, ⟨S, hS, rfl, rfl⟩, prod_image_toNat hp hq hpq S⟩
  · rintro ⟨A, t, ⟨S, hS, hA, ht⟩, rfl⟩
    refine ⟨S.image (toNat p q), Finset.image_subset_image hS, ?_⟩
    rw [prod_image_toNat hp hq hpq, hA, ht]

/-- **Ang's property for `{p, q}`-smooth numbers.** Let `p ≠ q` be primes. If `m` and
`p ^ e * m` are products of subsets of the `{p, q}`-smooth numbers in `[1, n]`, then so is
`p ^ k * m` for every `k ≤ e`. -/
theorem ang_two_primes {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {m e k : ℕ}
    (h1 : ∃ s ⊆ smooth p q n, s.prod id = m)
    (h2 : ∃ s ⊆ smooth p q n, s.prod id = p ^ e * m) (hk : k ≤ e) :
    ∃ s ⊆ smooth p q n, s.prod id = p ^ k * m := by
  rw [prod_iff hp hq hpq] at h1 h2 ⊢
  obtain ⟨A₁, t₁, r₁, rfl⟩ := h1
  obtain ⟨A₂, t₂, r₂, h⟩ := h2
  -- compare exponents
  have heq : toNat p q (A₂, t₂) = toNat p q (A₁, t₁ + e) := by
    simp only [toNat]; rw [← h, pow_add]; ring
  have hA := congrArg Prod.fst (toNat_injective hp hq hpq heq)
  have ht := congrArg Prod.snd (toNat_injective hp hq hpq heq)
  simp only at hA ht
  rw [hA, ht] at r₂
  -- the case `n = 0`
  by_cases hn : n = 0
  · subst hn
    have hk0 : k = 0 := by
      obtain ⟨S, hS, _, hS2⟩ := r₂
      have hS0 : S = ∅ := by
        apply Finset.subset_empty.mp
        intro x hx
        have := hS hx
        unfold expPairs at this
        simp only [Finset.mem_filter] at this
        have h3 : 0 < q ^ x.1 * p ^ x.2 := Nat.mul_pos (pow_pos hq.pos _) (pow_pos hp.pos _)
        omega
      subst hS0
      simp at hS2
      omega
    subst hk0
    exact ⟨A₁, t₁, r₁, by ring⟩
  -- the skyline argument
  have hsky := expPairs_eq_sky hp hq (n := n) (by omega)
  rw [hsky] at r₁ r₂ ⊢
  have hint := Skyline.reach_interval (K := Nat.log q n)
    (h := fun a => Nat.log p (n / q ^ a) + 1) (fun _ _ => by omega) A₁
  exact ⟨A₁, t₁ + k, hint t₁ (t₁ + e) (t₁ + k) r₁ r₂ (by omega) (by omega), by
    rw [pow_add]; ring⟩

end TwoPrimes
