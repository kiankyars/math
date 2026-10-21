import OpenProblem.WOWII96

/-!
# Written on the Wall II, Conjecture 310

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 310.** If `G` is a simple connected graph such that `n(G) > 2`, then
> `γ_t(G) ≤ CEIL[1 + Tdist_min(v)/3]`.

Here `γ_t` is the total domination number, `Tdist(v) = ∑_u d(v, u)` is the total distance of
`v`, and `Tdist_min` is its minimum over all vertices.

We prove the conjecture (`conjecture310`), in the stronger form `3 γ_t ≤ Tdist(v) + 5` for every
vertex `v` (`three_mul_totalDomNum_le`).

* If `v` is adjacent to every other vertex, then `v` and one neighbour form a total dominating
  set.
* Otherwise some vertex is at distance two from `v`. Let `A`, `B`, `C` be the vertices at distance
  `1`, `2` and `≥ 3` from `v`, and give every vertex of `B ∪ C` a parent one step closer to `v`.
  Then `v` together with all parents is a total dominating set. The parents of `B` lie in `A`, so
  there are at most `min(|A|, |B|) + |C| ≤ (|A| + 2|B| + 3|C|) / 3 ≤ Tdist(v) / 3` parents.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII310

open SimpleGraph WOWII372 WOWII320

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- If some vertex is at distance at least two from `v`, then some vertex is at distance exactly
two. -/
lemma exists_dist_two {G : SimpleGraph V} (hG : G.Connected) (v : V) :
    ∀ k, ∀ u, G.dist v u = k + 2 → ∃ b, G.dist v b = 2 := by
  intro k
  induction k with
  | zero => exact fun u hu => ⟨u, hu⟩
  | succ k ih =>
    intro u hu
    have huv : u ≠ v := by
      rintro rfl
      rw [SimpleGraph.dist_self] at hu
      omega
    obtain ⟨p, -, hp⟩ := WOWII96.exists_parent hG v u huv
    exact ih p (by omega)

/-- `3 γ_t(G) ≤ Tdist(v) + 5` for every vertex `v` of a connected graph on at least two
vertices. -/
lemma three_mul_totalDomNum_le {G : SimpleGraph V} (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (v : V) : 3 * totalDomNum G ≤ Tdist G v + 5 := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hdist0 : ∀ u, G.dist v u = 0 → u = v := fun u h =>
    ((hG.preconnected v u).dist_eq_zero_iff.mp h).symm
  set A := univ.filter fun u => G.dist v u = 1
  set B := univ.filter fun u => G.dist v u = 2
  set C := univ.filter fun u => 3 ≤ G.dist v u
  -- `Tdist(v) ≥ |A| + 2|B| + 3|C|`
  have hT : #A + 2 * #B + 3 * #C ≤ Tdist G v := by
    have h1 : ∑ u ∈ A, G.dist v u = #A := by
      rw [card_eq_sum_ones]
      exact sum_congr rfl fun u hu => (mem_filter.mp hu).2
    have h2 : ∑ u ∈ B, G.dist v u = 2 * #B := by
      rw [card_eq_sum_ones, mul_sum]
      exact sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2, mul_one]
    have h3 : 3 * #C ≤ ∑ u ∈ C, G.dist v u := by
      rw [card_eq_sum_ones, mul_sum]
      exact sum_le_sum fun u hu => by rw [mul_one]; exact (mem_filter.mp hu).2
    have hAB : Disjoint A B := disjoint_filter.mpr fun u _ h1 h2 => by omega
    have hABC : Disjoint (A ∪ B) C := by
      rw [disjoint_union_left]
      exact ⟨disjoint_filter.mpr fun u _ h1 h2 => by omega,
        disjoint_filter.mpr fun u _ h1 h2 => by omega⟩
    have hsum := sum_le_sum_of_subset (f := fun u => G.dist v u) (subset_univ (A ∪ B ∪ C))
    rw [sum_union hABC, sum_union hAB, h1, h2] at hsum
    unfold Tdist
    omega
  by_cases hfar : ∃ u, 2 ≤ G.dist v u
  · -- some vertex is at distance two
    obtain ⟨u, hu⟩ := hfar
    obtain ⟨b, hb⟩ := exists_dist_two hG v (G.dist v u - 2) u (by omega)
    -- a parent for each vertex other than `v`
    let par : V → V := fun x => if hx : x ≠ v then (WOWII96.exists_parent hG v x hx).choose else v
    have hpar : ∀ x, x ≠ v → G.Adj (par x) x ∧ G.dist v (par x) + 1 = G.dist v x := by
      intro x hx
      simp only [par, hx, ne_eq, not_false_eq_true, dite_true]
      exact (WOWII96.exists_parent hG v x hx).choose_spec
    have hne : ∀ x, 2 ≤ G.dist v x → x ≠ v := by
      rintro x hx rfl
      rw [SimpleGraph.dist_self] at hx
      omega
    set P := (B ∪ C).image par
    have hS : IsTDS G (insert v P) := by
      intro x
      by_cases hxv : x = v
      · subst hxv
        have hpb := hpar b (hne b (by omega))
        refine ⟨par b, mem_insert_of_mem (mem_image_of_mem par (mem_union_left _ ?_)), ?_⟩
        · exact mem_filter.mpr ⟨mem_univ b, hb⟩
        · exact dist_eq_one_iff_adj.mp (by omega)
      · have hpos : G.dist v x ≠ 0 := fun h => hxv (hdist0 x h)
        by_cases h1 : G.dist v x = 1
        · exact ⟨v, mem_insert_self v P, (dist_eq_one_iff_adj.mp h1).symm⟩
        · refine ⟨par x, mem_insert_of_mem (mem_image_of_mem par ?_), (hpar x hxv).1.symm⟩
          by_cases h2 : G.dist v x = 2
          · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ x, h2⟩)
          · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ x, by omega⟩)
    -- counting the parents
    have hPB : B.image par ⊆ A := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      have hx2 := (mem_filter.mp hx).2
      have := (hpar x (hne x (by omega))).2
      exact mem_filter.mpr ⟨mem_univ _, by omega⟩
    have hP : #P ≤ #(B.image par) + #(C.image par) := by
      rw [show P = B.image par ∪ C.image par from image_union _ _]
      exact card_union_le _ _
    have hPB1 := card_le_card hPB
    have hPB2 : #(B.image par) ≤ #B := card_image_le
    have hPC : #(C.image par) ≤ #C := card_image_le
    have hγ : totalDomNum G ≤ #(insert v P) := Nat.sInf_le ⟨_, hS, rfl⟩
    have := card_insert_le v P
    omega
  · -- `v` is adjacent to every other vertex
    push Not at hfar
    obtain ⟨w, hwv⟩ := exists_ne v
    have hw1 : G.dist v w = 1 := by
      have := hfar w
      have : G.dist v w ≠ 0 := fun h => hwv (hdist0 w h)
      omega
    have hS : IsTDS G {v, w} := by
      intro x
      by_cases hxv : x = v
      · subst hxv
        exact ⟨w, by simp, dist_eq_one_iff_adj.mp hw1⟩
      · have : G.dist v x = 1 := by
          have := hfar x
          have : G.dist v x ≠ 0 := fun h => hxv (hdist0 x h)
          omega
        exact ⟨v, by simp, (dist_eq_one_iff_adj.mp this).symm⟩
    have hγ : totalDomNum G ≤ #({v, w} : Finset V) := Nat.sInf_le ⟨_, hS, rfl⟩
    have := card_le_two (a := v) (b := w)
    have hA : 1 ≤ #A := card_pos.mpr ⟨w, mem_filter.mpr ⟨mem_univ w, hw1⟩⟩
    omega

/-- **WOWII Conjecture 310.** For every connected graph on more than two vertices,
`γ_t(G) ≤ ⌈1 + Tdist_min / 3⌉`. -/
theorem conjecture310 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 < Fintype.card V) :
    (totalDomNum G : ℤ) ≤ ⌈(1 : ℝ) + (TdistMin G : ℝ) / 3⌉ := by
  have : Nonempty V := hG.nonempty
  obtain ⟨w, hw⟩ := Nat.sInf_mem (Set.range_nonempty (Tdist G))
  have h := three_mul_totalDomNum_le hG (by omega) w
  have hmin : TdistMin G = Tdist G w := hw.symm
  rw [Int.le_ceil_iff]
  have h' : (3 * totalDomNum G : ℝ) ≤ TdistMin G + 5 := by
    rw [hmin]
    exact_mod_cast h
  push_cast
  linarith

end WOWII310
