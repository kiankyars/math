import OpenProblem.WOWII96

/-!
# Written on the Wall II, Conjecture 169

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 169.** If `G` is a simple connected graph, then
> `L_s(G) ≥ 1 + maximum of dist_even(v) - minimum of dist_even(v)`.

Here `L_s` is the maximum number of leaves of a spanning tree and `dist_even(v)` the number of
vertices at even distance from `v` (including `v`).

We prove the conjecture (`conjecture169`).

* For a root `r`, the edges joining vertices at different distances from `r` form a connected
  spanning subgraph. It contains a spanning tree `T` in which every edge joins a vertex at even
  distance from `r` to one at odd distance (`exists_parity_tree`).
* In a tree, if every edge has exactly one end in `X`, then summing degrees over `X` gives
  `2|X| ≤ n - 1 + #(leaves in X)` (`two_mul_card_le`).

With `r` minimising `dist_even` and `X` the odd vertices, this gives `n - 2 min ≤ L_s - 1`. With
`r` maximising `dist_even` and `X` the even vertices, it gives `2 max - n ≤ L_s - 1`. Adding the
two inequalities proves the conjecture.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII169

open SimpleGraph WOWII178 WOWII320

variable {V : Type*} [Fintype V]

/-- In a tree in which every edge has exactly one end in `X`, `2|X| ≤ n - 1 + #(leaves in X)`. -/
lemma two_mul_card_le {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V)
    (X : Finset V) (hX : ∀ x y, T.Adj x y → (x ∈ X ↔ y ∉ X)) :
    2 * #X ≤ Fintype.card V - 1 + #(X.filter fun x => T.degree x = 1) := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos : ∀ x, 1 ≤ T.degree x := fun x => hT.connected.preconnected.degree_pos_of_nontrivial x
  -- the degrees over `X` count every edge once
  have hsum : ∑ x ∈ X, T.degree x = #T.edgeFinset := by
    have hdisj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        Disjoint (T.incidenceFinset x) (T.incidenceFinset y) := by
      intro x hx y hy hxy
      rw [Finset.disjoint_left]
      intro e hex hey
      rw [mem_incidenceFinset] at hex hey
      have he : e = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hex.2, hey.2⟩
      have hadj : T.Adj x y := by rw [← SimpleGraph.mem_edgeSet, ← he]; exact hex.1
      exact ((hX x y hadj).mp hx) hy
    rw [show ∑ x ∈ X, T.degree x = ∑ x ∈ X, #(T.incidenceFinset x) from
      sum_congr rfl fun x _ => (card_incidenceFinset_eq_degree T x).symm, ← card_biUnion hdisj]
    · congr 1
      ext e
      simp only [mem_biUnion, mem_incidenceFinset, mem_edgeFinset]
      constructor
      · rintro ⟨x, -, he, -⟩
        exact he
      · intro he
        induction e using Sym2.ind with
        | h a b =>
          by_cases ha : a ∈ X
          · exact ⟨a, ha, he, Sym2.mem_mk_left a b⟩
          · have hb : b ∈ X := by
              by_contra hb
              exact ha ((hX a b (T.mem_edgeSet.mp he)).mpr hb)
            exact ⟨b, hb, he, Sym2.mem_mk_right a b⟩
  -- each vertex has degree at least one, and at least two unless it is a leaf
  have hle : 2 * #X ≤ ∑ x ∈ X, T.degree x + #(X.filter fun x => T.degree x = 1) := by
    rw [card_eq_sum_ones X, mul_sum, card_eq_sum_ones (X.filter _), sum_filter,
      ← sum_add_distrib]
    simp only [mul_one]
    apply sum_le_sum
    intro x _
    have := hpos x
    split_ifs <;> omega
  have hE := hT.card_edgeFinset
  omega

omit [Fintype V] in
/-- A spanning tree of a connected graph in which every edge joins a vertex at even distance from
`r` to one at odd distance. -/
lemma exists_parity_tree {G : SimpleGraph V} (hG : G.Connected) (r : V) :
    ∃ T ≤ G, T.IsTree ∧ ∀ x y, T.Adj x y → (Even (G.dist r x) ↔ ¬ Even (G.dist r y)) := by
  let H : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ G.dist r x ≠ G.dist r y
      symm := ⟨fun x y h => ⟨h.1.symm, Ne.symm h.2⟩⟩
      loopless := ⟨fun x h => h.2 rfl⟩ }
  have hHG : H ≤ G := fun x y h => h.1
  have hreach : ∀ k, ∀ x, G.dist r x = k → H.Reachable r x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hx
      by_cases hxr : x = r
      · rw [hxr]
      · obtain ⟨p, hpx, hp⟩ := WOWII96.exists_parent hG r x hxr
        have hHpx : H.Adj p x := ⟨hpx, by omega⟩
        exact (ih (G.dist r p) (by omega) p rfl).trans hHpx.reachable
  have hH : H.Connected := by
    have : Nonempty V := hG.nonempty
    exact ⟨fun x y => (hreach _ x rfl).symm.trans (hreach _ y rfl)⟩
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  refine ⟨T, hTH.trans hHG, hT, fun x y hxy => ?_⟩
  have hHxy := hTH hxy
  have h1 := WOWII96.dist_le_succ_of_adj hG r hHxy.1
  have h2 := WOWII96.dist_le_succ_of_adj hG r hHxy.1.symm
  have h3 := hHxy.2
  rcases Nat.lt_or_gt_of_ne h3 with h | h
  · have : G.dist r y = G.dist r x + 1 := by omega
    rw [this, Nat.even_add_one]
    tauto
  · have : G.dist r x = G.dist r y + 1 := by omega
    rw [this, Nat.even_add_one]

/-- **WOWII Conjecture 169.** For every connected graph on at least two vertices,
`L_s(G) ≥ 1 + max dist_even(v) - min dist_even(v)`. -/
theorem conjecture169 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    1 + maxDistEven G ≤ Ls G + sInf (Set.range (distEven G)) := by
  have : Nonempty V := hG.nonempty
  obtain ⟨w, hw⟩ := Nat.sInf_mem (Set.range_nonempty (distEven G))
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup univ univ_nonempty (distEven G)
  rw [← hw, maxDistEven, hu]
  -- the odd vertices from `w`
  obtain ⟨Tw, hTwG, hTw, hcw⟩ := exists_parity_tree hG w
  have h1 := two_mul_card_le hTw hn (univ.filter fun x => ¬ Even (G.dist w x)) (by
    intro x y hxy
    simp only [mem_filter, mem_univ, true_and, not_not]
    have := hcw x y hxy
    tauto)
  have hl1 : #((univ.filter fun x => ¬ Even (G.dist w x)).filter fun x => Tw.degree x = 1) ≤
      Ls G := (card_le_card fun x hx => by
        simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact hx.2).trans (le_Ls hTwG hTw)
  have hc1 : #(univ.filter fun x => ¬ Even (G.dist w x)) + distEven G w = Fintype.card V := by
    rw [distEven, add_comm, card_filter_add_card_filter_not, card_univ]
  -- the even vertices from `u`
  obtain ⟨Tu, hTuG, hTu, hcu⟩ := exists_parity_tree hG u
  have h2 := two_mul_card_le hTu hn (univ.filter fun x => Even (G.dist u x)) (by
    intro x y hxy
    simp only [mem_filter, mem_univ, true_and]
    exact hcu x y hxy)
  have hl2 : #((univ.filter fun x => Even (G.dist u x)).filter fun x => Tu.degree x = 1) ≤
      Ls G := (card_le_card fun x hx => by
        simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact hx.2).trans (le_Ls hTuG hTu)
  have hc2 : #(univ.filter fun x => Even (G.dist u x)) = distEven G u := rfl
  omega

end WOWII169
