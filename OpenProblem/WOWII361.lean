import OpenProblem.WOWII380

/-!
# Written on the Wall II, Conjecture 361

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 361.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ number of isolates of <S(T)> + |C|`, where `S(T)` is the set of support vertices of
> `T` and `C` is the center of `T`.

Here `γ_t` is the total domination number, a support vertex is a vertex adjacent to a leaf, and
`<S(T)>` is the subgraph induced by the support vertices. We prove it for all trees with at least
two vertices (`conjecture361`).

Let `D` be a minimum total dominating set. A leaf is dominated only by its neighbour, so `D`
contains every support vertex. A tree has at most two center vertices, and two of them are
adjacent (`WOWII380.center_adj`).

* If two support vertices are adjacent, neither is an isolate of `<S(T)>`. Then
  `|D| ≥ |S(T)| ≥ #isolates + 2`.
* Otherwise `S(T)` is independent, so every support vertex has a neighbour in `D - S(T)`, and
  `|D| ≥ |S(T)| + 1`. Suppose `D = S(T) ∪ {t}` and `T` has two centers.
  - Every support vertex is adjacent to `t`, and every vertex is adjacent to `t` or to a support
    vertex, so `ecc(t) ≤ 2`.
  - Two adjacent centers of eccentricity at most one would form a triangle with a third vertex.
    So the radius is `2`, and `t` is a center.
  - Every neighbour of `t` is a support vertex, since otherwise a triangle or a `4`-cycle appears.
    In particular the other center `c` is a support vertex.
  - Since `ecc(c) = 2`, a second neighbour of `t` would give a triangle. So `t` is a leaf at `c`,
    and then `ecc(c) ≤ 1`, a contradiction.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII361

open SimpleGraph WOWII372 WOWII377 WOWII380

variable {V : Type*} [Fintype V]

/-- The support vertices: the vertices adjacent to a leaf. -/
def supports (T : SimpleGraph V) : Finset V :=
  univ.filter fun v => ∃ w, T.Adj v w ∧ T.degree w = 1

/-- The isolates of the subgraph induced by the support vertices. -/
def isoSupports (T : SimpleGraph V) : Finset V :=
  (supports T).filter fun v => ∀ w ∈ supports T, ¬ T.Adj v w

/-- The statement of Conjecture 361. -/
def Conjecture361 : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → 2 < Fintype.card V →
    #(isoSupports T) + #(center T) ≤ totalDomNum T

/-! ### Short cycles -/

omit [Fintype V] in
/-- A tree has no triangle. -/
lemma no_triangle {T : SimpleGraph V} (hT : T.IsTree) {a b c : V} (hab : T.Adj a b)
    (hbc : T.Adj b c) (hca : T.Adj c a) : False := by
  have h1 := T.ne_of_adj hab
  have h2 := T.ne_of_adj hbc
  have h3 := T.ne_of_adj hca
  refine hT.isAcyclic (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))) ?_
  rw [Walk.cons_isCycle_iff]
  simp only [Walk.cons_isPath_iff, Walk.support_cons, Walk.support_nil, Walk.edges_cons,
    Walk.edges_nil, List.mem_cons, List.not_mem_nil, Sym2.eq_iff, Walk.IsPath.nil]
  grind

omit [Fintype V] in
/-- A tree has no `4`-cycle. -/
lemma no_square {T : SimpleGraph V} (hT : T.IsTree) {a b c d : V} (hab : T.Adj a b)
    (hbc : T.Adj b c) (hcd : T.Adj c d) (hda : T.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    False := by
  have h1 := T.ne_of_adj hab
  have h2 := T.ne_of_adj hbc
  have h3 := T.ne_of_adj hcd
  have h4 := T.ne_of_adj hda
  refine hT.isAcyclic
    (Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))) ?_
  rw [Walk.cons_isCycle_iff]
  simp only [Walk.cons_isPath_iff, Walk.support_cons, Walk.support_nil, Walk.edges_cons,
    Walk.edges_nil, List.mem_cons, List.not_mem_nil, Sym2.eq_iff, Walk.IsPath.nil]
  grind

/-! ### The proof -/

/-- **WOWII Conjecture 361**, for all trees with at least two vertices. -/
theorem conjecture361 (T : SimpleGraph V) (hT : T.IsTree) (hn : 1 < Fintype.card V) :
    #(isoSupports T) + #(center T) ≤ totalDomNum T := by
  have hconn := hT.connected
  have hpos := degree_pos hT (by omega)
  have hnbr : ∀ v, ∃ u, T.Adj v u := fun v => by
    have := hpos v
    rw [← card_neighborFinset_eq_degree] at this
    obtain ⟨u, hu⟩ := card_pos.mp this
    exact ⟨u, (T.mem_neighborFinset v u).mp hu⟩
  obtain ⟨D, hD, hDcard⟩ := exists_tds_card_eq hnbr
  rw [← hDcard]
  set S := supports T with hSdef
  -- the support vertices lie in every total dominating set
  have hSD : S ⊆ D := by
    intro s hs
    obtain ⟨w, hsw, hw⟩ := (mem_filter.mp hs).2
    obtain ⟨u, huD, hwu⟩ := hD w
    have : u = s := eq_of_degree_le_one hw.le hwu hsw.symm
    exact this ▸ huD
  -- a tree has at most two centers
  have hC2 : #(center T) ≤ 2 := by
    by_contra h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp (show 2 < #(center T) by omega)
    rcases center_adj hT ha hb with h1 | h1
    · exact hab h1
    rcases center_adj hT hb hc with h2 | h2
    · exact hbc h2
    rcases center_adj hT hc ha with h3 | h3
    · exact hac h3.symm
    exact no_triangle hT h1 h2 h3
  by_cases hA : ∃ s ∈ S, ∃ s' ∈ S, T.Adj s s'
  · -- two adjacent support vertices are not isolates
    obtain ⟨s, hs, s', hs', hss'⟩ := hA
    have hsub : isoSupports T ⊆ (S.erase s).erase s' := by
      intro v hv
      obtain ⟨hvS, hv⟩ := mem_filter.mp hv
      refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hvS⟩⟩
      · rintro rfl
        exact hv s hs hss'.symm
      · rintro rfl
        exact hv s' hs' hss'
    have h1 := card_le_card hsub
    have h2 : #((S.erase s).erase s') + 2 = #S := by
      have hs'S : s' ∈ S.erase s := mem_erase.mpr ⟨T.ne_of_adj hss'.symm, hs'⟩
      have h3 := card_erase_of_mem hs'S
      have h4 := card_erase_of_mem hs
      have h5 := card_pos.mpr ⟨s', hs'S⟩
      omega
    have := card_le_card hSD
    omega
  push Not at hA
  -- with two vertices both are adjacent support vertices
  have hn3 : 2 < Fintype.card V := by
    by_contra h2
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨u, hvu⟩ := hnbr v
    have hdeg : ∀ x, T.degree x = 1 := by
      intro x
      have h1 := hpos x
      have h3 : T.degree x ≤ 1 := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : T.neighborFinset x ⊆ univ.erase x := fun y hy =>
          mem_erase.mpr ⟨(T.ne_of_adj ((T.mem_neighborFinset x y).mp hy)).symm, mem_univ y⟩
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_univ x), card_univ] at this
        omega
      omega
    exact hA v (mem_filter.mpr ⟨mem_univ v, u, hvu, hdeg u⟩) u
      (mem_filter.mpr ⟨mem_univ u, v, hvu.symm, hdeg v⟩) hvu
  have hIS : isoSupports T = S := filter_true_of_mem fun v hv w hw => hA v hv w hw
  rw [hIS]
  -- `D` is not `S`, since `S` is independent
  have hDS : #S + 1 ≤ #D := by
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v⟩ := this
    obtain ⟨u, huD, -⟩ := hD v
    obtain ⟨u', hu'D, huu'⟩ := hD u
    by_contra hlt
    have hSeq : S = D := eq_of_subset_of_card_le hSD (by omega)
    rw [← hSeq] at huD hu'D
    exact hA u huD u' hu'D huu'
  by_contra hlt
  have hC : #(center T) = 2 := by omega
  -- `D = S ∪ {t}`
  obtain ⟨t, htD, htS⟩ : ∃ t ∈ D, t ∉ S := by
    by_contra h
    push Not at h
    have := card_le_card (show D ⊆ S from h)
    omega
  have hDt : ∀ x ∈ D, x ∈ S ∨ x = t := by
    intro x hx
    by_contra h
    push Not at h
    have hsub : insert t S ⊆ D.erase x := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_erase.mpr ⟨fun h' => h.2 h'.symm, htD⟩
      · exact mem_erase.mpr ⟨fun h' => h.1 (h' ▸ hy), hSD hy⟩
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem htS, card_erase_of_mem hx] at h1
    omega
  -- every support vertex is adjacent to `t`
  have hF1 : ∀ s ∈ S, T.Adj s t := by
    intro s hs
    obtain ⟨u, huD, hsu⟩ := hD s
    rcases hDt u huD with hu | rfl
    · exact absurd hsu (hA s hs u hu)
    · exact hsu
  -- every vertex is adjacent to `t` or to a support vertex
  have hF2 : ∀ v, T.Adj v t ∨ ∃ s ∈ S, T.Adj v s := by
    intro v
    obtain ⟨u, huD, hvu⟩ := hD v
    rcases hDt u huD with hu | rfl
    · exact Or.inr ⟨u, hu, hvu⟩
    · exact Or.inl hvu
  -- every neighbour of `t` is a support vertex
  have hnbrS : ∀ u, T.Adj t u → u ∈ S := by
    intro u htu
    by_contra huS
    have hu2 : 2 ≤ T.degree u := by
      by_contra h
      have h1 : T.degree u = 1 := by have := hpos u; omega
      exact htS (mem_filter.mpr ⟨mem_univ t, u, htu, h1⟩)
    obtain ⟨w, huw, hwt⟩ : ∃ w, T.Adj u w ∧ w ≠ t := by
      rw [← card_neighborFinset_eq_degree] at hu2
      obtain ⟨w, hw, hne⟩ := exists_mem_ne (by omega : 1 < #(T.neighborFinset u)) t
      exact ⟨w, (T.mem_neighborFinset u w).mp hw, hne⟩
    rcases hF2 w with hwt' | ⟨s, hs, hws⟩
    · exact no_triangle hT htu huw hwt'
    · refine no_square hT htu huw hws (hF1 s hs) (Ne.symm hwt) ?_
      rintro rfl
      exact huS hs
  -- `ecc(t) ≤ 2`
  have hecct : ecc T t ≤ 2 := by
    refine Finset.sup_le fun w _ => ?_
    rcases hF2 w with h | ⟨s, hs, h⟩
    · exact (T.dist_le (Walk.cons h.symm Walk.nil)).trans (by simp)
    · exact (T.dist_le (Walk.cons (hF1 s hs).symm (Walk.cons h.symm Walk.nil))).trans
        (by simp)
  -- the radius is at least two
  obtain ⟨c, hc, c', hc', hcc'⟩ := one_lt_card.mp (by omega : 1 < #(center T))
  have hrad : 2 ≤ rad T := by
    by_contra hlt2
    have hcr : ecc T c = rad T := (mem_filter.mp hc).2
    have hcr' : ecc T c' = rad T := (mem_filter.mp hc').2
    obtain ⟨w, hw, hwc⟩ := exists_mem_ne
      (by rw [card_erase_of_mem (mem_univ c), card_univ]; omega : 1 < #(univ.erase c)) c'
    have hwc' : w ≠ c := (mem_erase.mp hw).1
    have adj_of : ∀ x, ecc T x ≤ 1 → ∀ y, y ≠ x → T.Adj x y := by
      intro x hx y hyx
      have hd := (dist_le_ecc T x y).trans hx
      have hp := (hconn.preconnected x y).pos_dist_of_ne (Ne.symm hyx)
      exact dist_eq_one_iff_adj.mp (by omega)
    exact no_triangle hT (adj_of c (by omega) c' (Ne.symm hcc')) (adj_of c' (by omega) w hwc)
      (adj_of c (by omega) w hwc').symm
  -- `t` is a center, and the other center `c''` is adjacent to it
  have htC : t ∈ WOWII380.center T :=
    mem_filter.mpr ⟨mem_univ t, le_antisymm (by omega) (rad_le_ecc T t)⟩
  obtain ⟨c'', hc'', hc''t⟩ := exists_mem_ne (by omega : 1 < #(center T)) t
  have htc'' : T.Adj t c'' := (center_adj hT htC hc'').resolve_left (Ne.symm hc''t)
  have hecc'' : ecc T c'' = rad T := (mem_filter.mp hc'').2
  have hradt := rad_le_ecc T t
  -- `t` is a leaf at `c''`
  have hleaf : ∀ u, T.Adj t u → u = c'' := by
    intro u htu
    by_contra huc
    obtain ⟨ℓ, huℓ, hℓ⟩ := (mem_filter.mp (hnbrS u htu)).2
    have hd : T.dist c'' ℓ ≤ 2 := (dist_le_ecc T c'' ℓ).trans (by omega)
    rcases near_cases (hconn.preconnected c'' ℓ) hd with h | h | ⟨x, h1, h2⟩
    · subst h
      exact T.ne_of_adj htu (eq_of_degree_le_one hℓ.le htc''.symm huℓ.symm)
    · exact huc (eq_of_degree_le_one hℓ.le huℓ.symm h.symm)
    · have hxu : x = u := eq_of_degree_le_one hℓ.le h2.symm huℓ.symm
      subst hxu
      exact no_triangle hT htu h1.symm htc''.symm
  -- then `ecc(c'') ≤ 1`
  have : ecc T c'' ≤ 1 := by
    refine Finset.sup_le fun w _ => ?_
    rcases hF2 w with h | ⟨s, hs, h⟩
    · rw [hleaf w h.symm, dist_self]
      omega
    · have : s = c'' := hleaf s (hF1 s hs).symm
      subst this
      exact (dist_eq_one_iff_adj.mpr h.symm).le
  omega

/-- **WOWII Conjecture 361** in the form of the statement. -/
theorem conjecture361' : Conjecture361 := fun _ _ T hT hn => conjecture361 T hT (by omega)

end WOWII361
