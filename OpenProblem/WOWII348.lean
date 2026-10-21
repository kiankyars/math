import OpenProblem.WOWII372

/-!
# Written on the Wall II, Conjecture 348

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 348.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ (2/3) |N(D_2(T)) - D_2(T)|`, where `D_2 = {v | deg(v) = 2}`.

Here `γ_t` is the total domination number and `N(A)` is the set of vertices adjacent to some
vertex of `A`, so `N(D_2) - D_2` is the set of vertices of degree other than two that have a
neighbour of degree two. (Reading `N` as the closed neighbourhood gives the same set.)

We prove the stronger bound `3 γ_t(T) ≥ 2 |N(D_2) - D_2| + 2` (`conjecture348`), which is sharp,
for example for a star with one subdivided edge. Let `S` be a total dominating set and
`X = N(D_2) - D_2`.

* At most `|S|/2 - 1` edges of `T` avoid `S` (`WOWII372.card_noneIn_le`).
* `X` injects into `S` plus the edges avoiding `S`. A vertex `x ∈ X ∩ S` maps to itself.
  A vertex `x ∈ X - S` with a degree-two neighbour `d ∉ S` maps to the edge `xd`. Any other
  `x ∈ X - S` maps to a degree-two neighbour, which lies in `S`. Two vertices outside `S`
  cannot share a degree-two neighbour `d`, since then `d` would have no neighbour in `S`.

Hence `|X| ≤ |S| + |S|/2 - 1`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII348

open SimpleGraph WOWII372

variable {V : Type*} [Fintype V]

/-- The vertices of degree two. -/
def D2 (T : SimpleGraph V) : Finset V := univ.filter (fun v => T.degree v = 2)

/-- The open neighbourhood `N(A)` of a set `A` of vertices. -/
def nbhd (T : SimpleGraph V) (A : Finset V) : Finset V := univ.filter (fun v => ∃ a ∈ A, T.Adj v a)

/-- A vertex of degree two has no neighbours other than two given distinct ones. -/
lemma eq_or_eq_of_degree_eq_two {T : SimpleGraph V} {d x y u : V} (hd : T.degree d = 2)
    (hxy : x ≠ y) (hx : T.Adj d x) (hy : T.Adj d y) (hu : T.Adj d u) : u = x ∨ u = y := by
  rw [← card_neighborFinset_eq_degree] at hd
  obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp hd
  have hx' : x ∈ T.neighborFinset d := (T.mem_neighborFinset d x).mpr hx
  have hy' : y ∈ T.neighborFinset d := (T.mem_neighborFinset d y).mpr hy
  have hu' : u ∈ T.neighborFinset d := (T.mem_neighborFinset d u).mpr hu
  rw [hab, mem_insert, mem_singleton] at hx' hy' hu'
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> rcases hu' with rfl | rfl <;>
    simp_all

/-- For a total dominating set `S` of a tree, `2 |N(D_2) - D_2| + 2 ≤ 3 |S|`. -/
lemma card_le_of_tds {T : SimpleGraph V} (hT : T.IsTree) {S : Finset V} (hS : IsTDS T S) :
    2 * #(nbhd T (D2 T) \ D2 T) + 2 ≤ 3 * #S := by
  set X := nbhd T (D2 T) \ D2 T with hXdef
  have hX : ∀ x ∈ X, T.degree x ≠ 2 ∧ ∃ d, T.Adj x d ∧ T.degree d = 2 := by
    intro x hx
    simp only [hXdef, nbhd, D2, mem_sdiff, mem_filter, mem_univ, true_and] at hx
    obtain ⟨⟨d, hd, hxd⟩, hx2⟩ := hx
    exact ⟨hx2, d, hxd, hd⟩
  let Eout := T.edgeFinset.filter (NoneIn S)
  have hcount : 2 * #Eout + 2 ≤ #S := card_noneIn_le hT hS
  -- vertices of `X` outside `S` with a degree-two neighbour outside `S`
  let XA := X.filter (fun x => x ∉ S ∧ ∃ d, T.Adj x d ∧ T.degree d = 2 ∧ d ∉ S)
  let XB := X.filter (fun x => ¬ (x ∉ S ∧ ∃ d, T.Adj x d ∧ T.degree d = 2 ∧ d ∉ S))
  have hsplit : #XA + #XB = #X := Finset.card_filter_add_card_filter_not _
  -- `XA` injects into the edges avoiding `S`
  have hA : #XA ≤ #Eout := by
    have hA' : ∀ x ∈ XA, ∃ d, T.Adj x d ∧ T.degree d = 2 ∧ d ∉ S := fun x hx =>
      (mem_filter.mp hx).2.2
    choose! e he using hA'
    apply Finset.card_le_card_of_injOn (fun x => s(x, e x))
    · intro x hx
      obtain ⟨hxe, -, hes⟩ := he x hx
      have hxS : x ∉ S := (mem_filter.mp hx).2.1
      refine mem_filter.mpr ⟨T.mem_edgeFinset.mpr hxe, fun w hw => ?_⟩
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hxS
      · exact hes
    · intro x hx y hy hxy
      rcases Sym2.eq_iff.mp hxy with ⟨h, -⟩ | ⟨h1, -⟩
      · exact h
      · exact absurd (h1 ▸ (he y hy).2.1) (hX x (mem_filter.mp hx).1).1
  -- `XB` injects into `S`
  have hB : #XB ≤ #S := by
    choose! d hd using fun x (hx : x ∈ X) => (hX x hx).2
    apply Finset.card_le_card_of_injOn (fun x => if x ∈ S then x else d x)
    · intro x hx
      have hxX := (mem_filter.mp hx).1
      have hnot := (mem_filter.mp hx).2
      by_cases hxS : x ∈ S
      · simp [hxS]
      · simp only [hxS, ite_false]
        by_contra hdS
        exact hnot ⟨hxS, d x, (hd x hxX).1, (hd x hxX).2, hdS⟩
    · intro x hx y hy hxy
      have hxX := (mem_filter.mp hx).1
      have hyX := (mem_filter.mp hy).1
      by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S <;>
        simp only [hxS, hyS, ite_true, ite_false] at hxy
      · exact hxy
      · exact absurd (hxy ▸ (hd y hyX).2) (hX x hxX).1
      · exact absurd (hxy ▸ (hd x hxX).2) (hX y hyX).1
      · by_contra hne
        obtain ⟨u, huS, hu⟩ := hS (d x)
        have h1 : T.Adj (d x) x := (hd x hxX).1.symm
        have h2 : T.Adj (d x) y := hxy ▸ (hd y hyX).1.symm
        rcases eq_or_eq_of_degree_eq_two (hd x hxX).2 hne h1 h2 hu with rfl | rfl
        · exact hxS huS
        · exact hyS huS
  omega

/-- **WOWII Conjecture 348**, in the stronger form `3 γ_t(T) ≥ 2 |N(D_2(T)) - D_2(T)| + 2`,
for every tree `T` on at least two vertices. -/
theorem conjecture348 (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    2 * #(nbhd T (D2 T) \ D2 T) + 2 ≤ 3 * totalDomNum T := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnoiso : ∀ v, ∃ u, T.Adj v u := fun v =>
    (T.degree_pos_iff_exists_adj v).mp (hT.connected.preconnected.degree_pos_of_nontrivial v)
  obtain ⟨S, hS, hScard⟩ := exists_tds_card_eq hnoiso
  rw [← hScard]
  exact card_le_of_tds hT hS

/-- **WOWII Conjecture 348**, as stated: `γ_t(T) ≥ (2/3) |N(D_2(T)) - D_2(T)|` for every tree `T`
on more than two vertices. -/
theorem conjecture348_real (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 < Fintype.card V) :
    (2 / 3 : ℝ) * #(nbhd T (D2 T) \ D2 T) ≤ totalDomNum T := by
  have h : ((2 * #(nbhd T (D2 T) \ D2 T) + 2 : ℕ) : ℝ) ≤ ((3 * totalDomNum T : ℕ) : ℝ) := by
    exact_mod_cast conjecture348 T hT hn.le
  push_cast at h
  linarith

end WOWII348
