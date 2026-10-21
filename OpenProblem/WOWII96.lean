import OpenProblem.WOWII178
import OpenProblem.WOWII320

/-!
# Written on the Wall II, Conjecture 96

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 96.** If `G` is a simple connected graph, then
> `α(G) ≤ 1 + minimum dist_even(v) · (maximum of λ(v) - 1)`.

Here `α` is the independence number, `dist_even(v)` is the number of vertices at even distance
from `v` (including `v`), and `λ(v) = α(G[N(v)])` is the local independence number.

We prove the stronger statement that `α(G) ≤ 1 + dist_even(v) (λ_max - 1)` for *every* vertex
`v` (`indepNum_le`), which gives the conjecture (`conjecture96`).

Fix `v` and a maximum independent set `I`. Map each vertex of `I` at odd distance from `v` to a
neighbour one step closer to `v`, which is at even distance. Let `w` be a vertex at even distance.

* If `w ∈ I`, nothing maps to `w`.
* If `w ∉ I`, the vertices mapped to `w` form an independent subset of `N(w)`, so there are at
  most `λ(w)` of them.
* If moreover `w ≠ v`, the neighbour of `w` one step closer to `v` is at distance two from all of
  them, so it can be added to that independent set. Then at most `λ(w) - 1` vertices map to `w`.

Summing over the vertices at even distance, `|I| ≤ λ_max + (dist_even(v) - 1)(λ_max - 1)`.
If `λ_max = 1`, then `G` is complete and `α(G) = 1`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII96

open SimpleGraph WOWII178 WOWII320

variable {V : Type*} [Fintype V]

/-- An independent subset of `N(w)` has at most `λ(w)` vertices. -/
lemma card_le_localIndep (G : SimpleGraph V) (w : V) {A : Finset V} (hA : ∀ x ∈ A, G.Adj w x)
    (hind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) : #A ≤ localIndep G w := by
  let A' : Finset (G.neighborSet w) := A.subtype (· ∈ G.neighborSet w)
  have hcard : #A' = #A := by
    rw [card_subtype]
    congr 1
    exact filter_true_of_mem fun x hx => hA x hx
  have hI : (G.induce (G.neighborSet w)).IsIndepSet (A' : Set (G.neighborSet w)) := by
    intro x hx y hy _ hxy
    exact hind x.1 (mem_subtype.mp hx) y.1 (mem_subtype.mp hy) hxy
  rw [← hcard]
  exact hI.card_le_indepNum

lemma localIndep_le_max (G : SimpleGraph V) (w : V) : localIndep G w ≤ maxLocalIndep G :=
  Finset.le_sup (f := localIndep G) (mem_univ w)

omit [Fintype V] in
/-- A vertex other than `v` has a neighbour one step closer to `v`. -/
lemma exists_parent {G : SimpleGraph V} (hG : G.Connected) (v u : V) (hu : u ≠ v) :
    ∃ p, G.Adj p u ∧ G.dist v p + 1 = G.dist v u := by
  obtain ⟨q, hq⟩ := (hG.preconnected u v).exists_walk_length_eq_dist
  cases q with
  | nil => exact absurd rfl hu
  | @cons _ p _ h r =>
    refine ⟨p, h.symm, ?_⟩
    have h1 := G.dist_le r
    have h2 := hG.dist_triangle (u := v) (v := p) (w := u)
    rw [dist_eq_one_iff_adj.mpr h.symm] at h2
    rw [Walk.length_cons] at hq
    rw [G.dist_comm] at h1
    rw [show G.dist u v = G.dist v u from G.dist_comm] at hq
    omega

omit [Fintype V] in
lemma dist_le_succ_of_adj {G : SimpleGraph V} (hG : G.Connected) (v : V) {a b : V}
    (h : G.Adj a b) : G.dist v b ≤ G.dist v a + 1 := by
  have := hG.dist_triangle (u := v) (v := a) (w := b)
  rwa [dist_eq_one_iff_adj.mpr h] at this

/-- If `λ_max ≤ 1`, a connected graph has independence number at most one. -/
lemma indepNum_le_one {G : SimpleGraph V} (hG : G.Connected) (h : maxLocalIndep G ≤ 1) :
    G.indepNum ≤ 1 := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  rw [← hI.card_eq]
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hlt
  have hnadj : ¬ G.Adj a b := hI.isIndepSet ha hb hab
  -- a vertex at distance two from `a`
  have h2 : ∀ k, ∀ y, G.dist a y = k + 2 → ∃ z, G.dist a z = 2 := by
    intro k
    induction k with
    | zero => exact fun y hy => ⟨y, hy⟩
    | succ k ih =>
      intro y hy
      obtain ⟨p, -, hp⟩ := exists_parent hG a y
        (by intro h; rw [h, SimpleGraph.dist_self] at hy; omega)
      exact ih p (by omega)
  have hdab : 2 ≤ G.dist a b := WOWII378.two_le_dist (hG.preconnected a b) hab hnadj
  obtain ⟨z, hz⟩ := h2 (G.dist a b - 2) b (by omega)
  obtain ⟨x, hxz, hx⟩ := exists_parent hG a z
    (by intro h; rw [h, SimpleGraph.dist_self] at hz; omega)
  have hax : G.Adj a x := dist_eq_one_iff_adj.mp (by omega)
  have hanz : ¬ G.Adj a z := fun h => by rw [dist_eq_one_iff_adj.mpr h] at hz; omega
  have haz : a ≠ z := fun h => by rw [← h, SimpleGraph.dist_self] at hz; omega
  have := card_le_localIndep G x (A := {a, z})
    (by intro y hy; rcases mem_insert.mp hy with rfl | hy
        · exact hax.symm
        · rw [mem_singleton.mp hy]; exact hxz)
    (by intro y hy y' hy'
        simp only [mem_insert, mem_singleton] at hy hy'
        rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
        · exact G.irrefl
        · exact hanz
        · exact fun h => hanz h.symm
        · exact G.irrefl)
  rw [card_pair haz] at this
  have := localIndep_le_max G x
  omega

/-- For every vertex `v` of a connected graph, `α(G) ≤ 1 + dist_even(v) (λ_max - 1)`. -/
theorem indepNum_le {G : SimpleGraph V} (hG : G.Connected) (v : V) :
    G.indepNum ≤ 1 + distEven G v * (maxLocalIndep G - 1) := by
  rcases Nat.lt_or_ge (maxLocalIndep G) 2 with hl | hl
  · have := indepNum_le_one hG (by omega)
    omega
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  rw [← hI.card_eq]
  have hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := fun x hx y hy h =>
    hI.isIndepSet hx hy (G.ne_of_adj h) h
  set E := univ.filter fun u => Even (G.dist v u)
  set IO := I.filter fun u => ¬ Even (G.dist v u)
  -- parents of the odd vertices of `I`
  have hpar : ∀ u ∈ IO, ∃ p, G.Adj p u ∧ G.dist v p + 1 = G.dist v u := by
    intro u hu
    refine exists_parent hG v u fun h => ?_
    have := (mem_filter.mp hu).2
    rw [h, SimpleGraph.dist_self] at this
    exact this (by decide : Even 0)
  choose! par hpadj hpdist using hpar
  have hparE : ∀ u ∈ IO, par u ∈ E := by
    intro u hu
    have h1 := hpdist u hu
    have h2 := (mem_filter.mp hu).2
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [← h1, Nat.even_add_one] at h2
    exact not_not.mp h2
  set fib := fun w => IO.filter fun u => par u = w
  -- split `I` into its even and odd parts
  have hsplit : #I = #(I.filter fun u => Even (G.dist v u)) + #IO :=
    (card_filter_add_card_filter_not _).symm
  have hIE : #(I.filter fun u => Even (G.dist v u)) = ∑ w ∈ E, if w ∈ I then 1 else 0 := by
    rw [sum_boole, Nat.cast_id]
    congr 1
    ext u
    simp [E, and_comm]
  have hIO : #IO = ∑ w ∈ E, #(fib w) := card_eq_sum_card_fiberwise hparE
  -- the bound for each vertex at even distance
  have hterm : ∀ w ∈ E, (if w ∈ I then 1 else 0) + #(fib w) ≤
      (maxLocalIndep G - 1) + (if w = v then 1 else 0) := by
    intro w hwE
    have hfibN : ∀ u ∈ fib w, G.Adj w u := by
      intro u hu
      have := mem_filter.mp hu
      rw [← this.2]
      exact hpadj u this.1
    have hfibI : ∀ u ∈ fib w, u ∈ I := fun u hu => (mem_filter.mp (mem_filter.mp hu).1).1
    by_cases hwI : w ∈ I
    · have hempty : fib w = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        exact hind w hwI u (hfibI u hu) (hfibN u hu)
      simp only [hwI, ↓reduceIte, hempty, card_empty]
      split_ifs <;> omega
    · simp only [hwI, ↓reduceIte, zero_add]
      have hle := card_le_localIndep G w hfibN fun x hx y hy => hind x (hfibI x hx) y (hfibI y hy)
      have hmax := localIndep_le_max G w
      by_cases hwv : w = v
      · subst hwv
        simp only [↓reduceIte]
        omega
      · simp only [hwv, ↓reduceIte, add_zero]
        -- the parent `q` of `w` extends the independent set
        obtain ⟨q, hqw, hqd⟩ := exists_parent hG v w hwv
        have hfibd : ∀ u ∈ fib w, G.dist v u = G.dist v w + 1 := by
          intro u hu
          have := mem_filter.mp hu
          rw [← this.2]
          exact (hpdist u this.1).symm
        have hqnot : q ∉ fib w := fun h => by have := hfibd q h; omega
        have hle2 := card_le_localIndep G w (A := insert q (fib w))
          (by intro y hy
              rcases mem_insert.mp hy with rfl | hy
              · exact hqw.symm
              · exact hfibN y hy)
          (by intro y hy y' hy'
              have hq_far : ∀ u ∈ fib w, ¬ G.Adj q u := fun u hu h => by
                have := dist_le_succ_of_adj hG v h
                have := hfibd u hu
                omega
              rw [mem_insert] at hy hy'
              rcases hy with hy | hy <;> rcases hy' with hy' | hy'
              · rw [hy, hy']; exact G.irrefl
              · rw [hy]; exact hq_far y' hy'
              · rw [hy']; exact fun h => hq_far y hy h.symm
              · exact hind y (hfibI y hy) y' (hfibI y' hy'))
        rw [card_insert_of_notMem hqnot] at hle2
        omega
  have hvE : v ∈ E :=
    mem_filter.mpr ⟨mem_univ v, by rw [SimpleGraph.dist_self]; exact (by decide : Even 0)⟩
  have htotal : #I ≤ ∑ w ∈ E, ((maxLocalIndep G - 1) + (if w = v then 1 else 0)) := by
    rw [hsplit, hIE, hIO, ← sum_add_distrib]
    exact sum_le_sum hterm
  rw [sum_add_distrib, sum_const, smul_eq_mul, sum_ite_eq' E v (fun _ => 1)] at htotal
  simp only [hvE, ↓reduceIte] at htotal
  have : distEven G v = #E := rfl
  rw [this]
  nlinarith

/-- **WOWII Conjecture 96.** For every connected graph,
`α(G) ≤ 1 + minimum dist_even(v) · (maximum of λ(v) - 1)`. -/
theorem conjecture96 (G : SimpleGraph V) (hG : G.Connected) :
    G.indepNum ≤ 1 + sInf (Set.range (distEven G)) * (maxLocalIndep G - 1) := by
  have : Nonempty V := hG.nonempty
  obtain ⟨v, hv⟩ := Nat.sInf_mem (Set.range_nonempty (distEven G))
  rw [← hv]
  exact indepNum_le hG v

end WOWII96
