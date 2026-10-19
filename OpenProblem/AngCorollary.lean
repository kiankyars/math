import OpenProblem.TwoPrimes

/-!
# Ang's conjecture when the `p`-free part is a prime power

`OeisA60957.conjecture` in google-deepmind/formal-conjectures states, for the set
`productsOfSubsets n` of products of subsets of `{1, …, n}`: if `p ≤ n` is prime and
`m`, `p ^ a * m` are such products, then so is `p ^ k * m` for `0 < k < a`.

We prove this statement under the extra hypothesis that `m = q ^ A * p ^ t` for some prime
`q ≠ p`, i.e. that the `p`-free part of `m` is a prime power. This includes `p`-free part
`1`, by taking `A = 0`. Every subset whose product is `m` or `p ^ a * m` then consists of
`{p, q}`-smooth numbers, and `TwoPrimes.ang_two_primes` applies.
-/

open Finset

namespace AngCorollary

/-- The set of products of subsets of `{1, …, n}`, as in `OeisA60957.productsOfSubsets`. -/
def productsOfSubsets (n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ s ⊆ Finset.Icc 1 n, m = s.prod id}

lemma eq_pow_mul_pow_of_dvd {p q x A t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hx : x ∣ q ^ A * p ^ t) : ∃ a b, x = q ^ a * p ^ b := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hx
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hq).mp hy
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hz
  exact ⟨a, b, rfl⟩

/-- A subset of `{1, …, n}` whose product is `q ^ A * p ^ t` consists of `{p, q}`-smooth
numbers. -/
lemma subset_smooth {p q n A t : ℕ} (hp : p.Prime) (hq : q.Prime) {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 n) (hprod : s.prod id = q ^ A * p ^ t) :
    s ⊆ TwoPrimes.smooth p q n := by
  intro x hx
  rw [TwoPrimes.mem_smooth hp hq]
  refine ⟨(Finset.mem_Icc.mp (hs hx)).2, ?_⟩
  apply eq_pow_mul_pow_of_dvd hp hq (A := A) (t := t)
  rw [← hprod]
  exact Finset.dvd_prod_of_mem id hx

lemma smooth_subset_Icc {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) :
    TwoPrimes.smooth p q n ⊆ Finset.Icc 1 n := by
  intro x hx
  obtain ⟨hle, a, b, rfl⟩ := (TwoPrimes.mem_smooth hp hq).mp hx
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hp.ne_zero)), hle⟩

/-- **Ang's conjecture (OEIS A060957) when the `p`-free part of `m` is a prime power.**
Same statement as `OeisA60957.conjecture`, with the extra hypothesis
`m = q ^ A * p ^ t` for a prime `q ≠ p`. -/
theorem conjecture_of_prime_power_part (n p : ℕ) (hp : p.Prime) (_hpn : p ≤ n)
    (q A t : ℕ) (hq : q.Prime) (hpq : p ≠ q) (m a_exp : ℕ) (hm : m = q ^ A * p ^ t)
    (h1 : m ∈ productsOfSubsets n) (h2 : p ^ a_exp * m ∈ productsOfSubsets n)
    (k : ℕ) (_hk1 : 0 < k) (hk2 : k < a_exp) :
    p ^ k * m ∈ productsOfSubsets n := by
  obtain ⟨s₁, hs₁, hp₁⟩ := h1
  obtain ⟨s₂, hs₂, hp₂⟩ := h2
  have hsm₁ : s₁ ⊆ TwoPrimes.smooth p q n :=
    subset_smooth hp hq hs₁ (A := A) (t := t) (by rw [← hp₁, hm])
  have hsm₂ : s₂ ⊆ TwoPrimes.smooth p q n :=
    subset_smooth hp hq hs₂ (A := A) (t := t + a_exp) (by rw [← hp₂, hm, pow_add]; ring)
  obtain ⟨s, hs, hprod⟩ := TwoPrimes.ang_two_primes hp hq hpq (m := m) (e := a_exp) (k := k)
    ⟨s₁, hsm₁, hp₁.symm⟩ ⟨s₂, hsm₂, hp₂.symm⟩ hk2.le
  exact ⟨s, hs.trans (smooth_subset_Icc hp hq), hprod.symm⟩

end AngCorollary
