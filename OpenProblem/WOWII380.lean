import OpenProblem.WOWII367

/-!
# Written on the Wall II, Conjectures 380 and 241

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 380.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ |D_even(T)| / (ecc(C) - 1)`, where `C` is the center of `T` and `D_even(T)` is the
> set of vertices of even degree.

> **Conjecture 241.** If `G` is a tree, then
> `γ_t(G) ≥ FLOOR[number of components(<N[S]>) + dist_avg(C)]`, where `<N[S]>` is the subgraph
> induced by the closed neighbourhood of the set `S` of vertices of degree two and `C` is the set
> of center vertices.

We prove both. For 380 we accept two readings of `ecc(C)`: the eccentricity `max_v d(v, C)` of
the set `C` (`conjecture380`), and the common eccentricity of the center vertices, i.e. the
radius (`conjecture380_rad`). The value `x / 0` is `0`. For 241, `dist_avg(C)` is the mean
distance between distinct center vertices, as `dist_avg(V)` is the average distance of a graph
(`conjecture241`).

The proofs use the following facts about a tree `T` and a total dominating set `S`.

* Two center vertices are equal or adjacent (`center_adj`). If `c, c'` were further apart, the
  second vertex `m` of the `c`–`c'` path would have smaller eccentricity: every path from a
  vertex to `c` or to `c'` passes through `m`.
* Every tree satisfies `#non-leaves ≤ 2|S| - 2` (`WOWII367.nonleaves_le`). If every vertex lies
  within distance two of the center, then every non-leaf outside the center is a support vertex.
  In that case `#non-leaves ≤ |S|` (`nonleaves_le_of_near`).
* The subgraph `<N[S]>` has at most `|S| - 1` components (`numComp_add_one_le`). Each component
  contains a vertex of `S`. If each contained exactly one, those vertices would need neighbours
  in `S` outside `N[S]`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII380

open SimpleGraph WOWII372 WOWII377 WOWII378

variable {V : Type*} [Fintype V]

/-! ### Eccentricity and the center -/

/-- The eccentricity of a vertex. -/
def ecc (T : SimpleGraph V) (v : V) : ℕ := univ.sup fun w => T.dist v w

/-- The radius: the least eccentricity. -/
def rad (T : SimpleGraph V) : ℕ := sInf (Set.range (ecc T))

/-- The center: the vertices of least eccentricity. -/
def center (T : SimpleGraph V) : Finset V := univ.filter fun v => ecc T v = rad T

/-- The eccentricity of a set `A`: the largest distance from a vertex to `A`. -/
def eccSet (T : SimpleGraph V) (A : Finset V) : ℕ := univ.sup fun v => distToSet T v A

lemma dist_le_ecc (T : SimpleGraph V) (v w : V) : T.dist v w ≤ ecc T v :=
  Finset.le_sup (f := fun w => T.dist v w) (mem_univ w)

lemma rad_le_ecc (T : SimpleGraph V) (v : V) : rad T ≤ ecc T v := Nat.sInf_le ⟨v, rfl⟩

lemma center_nonempty (T : SimpleGraph V) [Nonempty V] : (center T).Nonempty := by
  obtain ⟨v, hv⟩ := Nat.sInf_mem (Set.range_nonempty (ecc T))
  exact ⟨v, mem_filter.mpr ⟨mem_univ v, hv⟩⟩

omit [Fintype V] in
/-- In a tree, every walk from `x` to an adjacent `y` uses the edge `xy`. -/
lemma mem_edges_of_adj {T : SimpleGraph V} (hT : T.IsTree) {x y : V} (h : T.Adj x y)
    (p : T.Walk x y) : s(x, y) ∈ p.edges :=
  isBridge_iff_forall_walk_mem_edges.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic h) p

/-- In a tree, two center vertices are equal or adjacent. -/
lemma center_adj {T : SimpleGraph V} (hT : T.IsTree) {c c' : V} (hc : c ∈ center T)
    (hc' : c' ∈ center T) : c = c' ∨ T.Adj c c' := by
  by_contra h
  push Not at h
  obtain ⟨hne, hnadj⟩ := h
  have hcr : ecc T c = rad T := (mem_filter.mp hc).2
  have hcr' : ecc T c' = rad T := (mem_filter.mp hc').2
  have hconn := hT.connected
  obtain ⟨q⟩ := hconn.preconnected c c'
  set p := q.bypass with hpdef
  have hp : p.IsPath := q.bypass_isPath
  -- the path has length at least two
  have hlen : 2 ≤ p.length := by
    have h2 := two_le_dist (hconn.preconnected c c') hne hnadj
    have := T.dist_le p
    omega
  set m := p.getVert 1
  have hm_supp : m ∈ p.support := p.getVert_mem_support 1
  have hmc : m ≠ c := by
    intro h
    have := hp.getVert_injOn (by simp; omega : 1 ∈ {i | i ≤ p.length})
      (by simp : 0 ∈ {i | i ≤ p.length}) (by rw [Walk.getVert_zero]; exact h)
    omega
  have hmc' : m ≠ c' := by
    intro h
    have := hp.getVert_injOn (by simp; omega : 1 ∈ {i | i ≤ p.length})
      (by simp : p.length ∈ {i | i ≤ p.length}) (by rw [Walk.getVert_length]; exact h)
    omega
  -- every vertex is closer to `m` than to `c` or to `c'`
  have key : ∀ w, T.dist w m + 1 ≤ rad T := by
    intro w
    obtain ⟨Pc, hPc⟩ := (hconn.preconnected w c).exists_walk_length_eq_dist
    obtain ⟨Pc', hPc'⟩ := (hconn.preconnected w c').exists_walk_length_eq_dist
    have hthrough : m ∈ Pc.support ∨ m ∈ Pc'.support := by
      by_contra hno
      push Not at hno
      let r := Pc.reverse.append Pc'
      have hr : m ∉ r.support := by
        intro hmr
        rw [Walk.support_append, Walk.support_reverse, List.mem_append, List.mem_reverse] at hmr
        rcases hmr with h | h
        · exact hno.1 h
        · exact hno.2 (List.mem_of_mem_tail h)
      have huniq : p = r.bypass := by
        have := (hT.isAcyclic.subsingleton_path c c').elim ⟨p, hp⟩ ⟨r.bypass, r.bypass_isPath⟩
        exact congrArg Subtype.val this
      exact hr (r.support_bypass_subset_support (huniq ▸ hm_supp))
    rcases hthrough with h | h
    · have hsplit := congrArg Walk.length (Pc.take_spec h)
      rw [Walk.length_append] at hsplit
      have h1 := T.dist_le (Pc.takeUntil m h)
      have h2 := T.dist_le (Pc.dropUntil m h)
      have h3 := (hconn.preconnected m c).pos_dist_of_ne hmc
      have h4 := dist_le_ecc T c w
      rw [T.dist_comm] at h4
      omega
    · have hsplit := congrArg Walk.length (Pc'.take_spec h)
      rw [Walk.length_append] at hsplit
      have h1 := T.dist_le (Pc'.takeUntil m h)
      have h2 := T.dist_le (Pc'.dropUntil m h)
      have h3 := (hconn.preconnected m c').pos_dist_of_ne hmc'
      have h4 := dist_le_ecc T c' w
      rw [T.dist_comm] at h4
      omega
  have hecc : ecc T m + 1 ≤ rad T := by
    have h0 := key m
    have : ecc T m ≤ rad T - 1 := Finset.sup_le fun w _ => by
      have := key w; rw [T.dist_comm]; omega
    omega
  have := rad_le_ecc T m
  omega

/-! ### Trees within distance two of a central clique -/

omit [Fintype V] in
lemma near_cases {T : SimpleGraph V} {v c : V} (hr : T.Reachable v c) (h : T.dist v c ≤ 2) :
    v = c ∨ T.Adj v c ∨ ∃ u, T.Adj v u ∧ T.Adj u c := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp] at h
  cases p with
  | nil => exact Or.inl rfl
  | cons h1 q =>
    cases q with
    | nil => exact Or.inr (Or.inl h1)
    | cons h2 q' =>
      cases q' with
      | nil => exact Or.inr (Or.inr ⟨_, h1, h2⟩)
      | cons _ _ => simp only [Walk.length_cons] at h; omega

/-- If every vertex of a tree is within distance two of a set `C` of pairwise adjacent vertices,
then a total dominating set has at least as many vertices as there are non-leaves. -/
lemma nonleaves_le_of_near {T : SimpleGraph V} (hT : T.IsTree) {C : Finset V}
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c = c' ∨ T.Adj c c')
    (hnear : ∀ v, v ∈ C ∨ (∃ c ∈ C, T.Adj v c) ∨ ∃ u c, c ∈ C ∧ T.Adj v u ∧ T.Adj u c)
    {S : Finset V} (hS : IsTDS T S) :
    #(univ.filter fun v => ¬ T.degree v ≤ 1) ≤ #S := by
  have hbr : ∀ {x y : V} (h : T.Adj x y) (p : T.Walk x y), s(x, y) ∈ p.edges :=
    fun h p => mem_edges_of_adj hT h p
  -- walks inside `C`
  have hwC : ∀ c ∈ C, ∀ c' ∈ C, ∃ q : T.Walk c c', ∀ z ∈ q.support, z ∈ C := by
    intro c hc c' hc'
    rcases hC c hc c' hc' with rfl | h
    · exact ⟨Walk.nil, fun z hz => by
        rw [Walk.support_nil, List.mem_singleton] at hz; rw [hz]; exact hc⟩
    · exact ⟨Walk.cons h Walk.nil, fun z hz => by
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hz
        rcases hz with rfl | rfl <;> assumption⟩
  have hnotC : ∀ {c c' : V} (q : T.Walk c c'), (∀ z ∈ q.support, z ∈ C) →
      ∀ {x y : V}, x ∉ C → s(x, y) ∉ q.edges := fun q hq _ _ hx he =>
    hx (hq _ (q.fst_mem_support_of_mem_edges he))
  -- (a) a vertex outside `C` has at most one neighbour in `C`
  have hA : ∀ u, u ∉ C → ∀ c ∈ C, ∀ c' ∈ C, T.Adj u c → T.Adj u c' → c = c' := by
    intro u hu c hc c' hc' h1 h2
    by_contra hne
    rcases hC c' hc' c hc with h | h
    · exact hne h.symm
    have := hbr h1 (Walk.cons h2 (Walk.cons h Walk.nil))
    simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false]
      at this
    rcases this with h3 | h3 <;> rcases Sym2.eq_iff.mp h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · exact hne h5
    · exact hu (by rw [h4]; exact hc')
    · exact hu (by rw [h4]; exact hc')
    · exact hu (by rw [h4]; exact hc)
  -- (b) no two vertices adjacent to `C` but outside it are adjacent
  have hB : ∀ u u', u ∉ C → u' ∉ C → ∀ c ∈ C, ∀ c' ∈ C, T.Adj u c → T.Adj u' c' →
      ¬ T.Adj u' u := by
    intro u u' hu hu' c hc c' hc' h1 h2 h
    obtain ⟨q, hq⟩ := hwC c' hc' c hc
    have := hbr h (Walk.cons h2 (q.append (Walk.cons h1.symm Walk.nil)))
    simp only [Walk.edges_cons, Walk.edges_append, Walk.edges_nil, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at this
    rcases this with h3 | h3 | h3
    · rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
      · exact hu (by rw [h4]; exact hc')
      · exact hu' (by rw [h4]; exact hc')
    · exact hnotC q hq hu' h3
    · rcases Sym2.eq_iff.mp h3 with ⟨h4, -⟩ | ⟨-, h4⟩
      · exact hu' (by rw [h4]; exact hc)
      · exact hu (by rw [h4]; exact hc)
  -- (c) a vertex outside `C` and not adjacent to `C` is a leaf
  have hL2 : ∀ x, x ∉ C → (¬ ∃ c ∈ C, T.Adj x c) → T.degree x ≤ 1 := by
    intro x hx hnadj
    obtain ⟨u, c, hc, hxu, huc⟩ : ∃ u c, c ∈ C ∧ T.Adj x u ∧ T.Adj u c := by
      rcases hnear x with h | h | h
      · exact absurd h hx
      · exact absurd h hnadj
      · exact h
    have hu : u ∉ C := fun huC => hnadj ⟨u, huC, hxu⟩
    rw [← card_neighborFinset_eq_degree]
    calc #(T.neighborFinset x) ≤ #({u} : Finset V) := by
          apply card_le_card
          intro y hy
          have hxy : T.Adj x y := (T.mem_neighborFinset x y).mp hy
          rw [mem_singleton]
          by_contra hyu
          have hxne : x ≠ y := T.ne_of_adj hxy
          have hyC : y ∉ C := fun hyC => hnadj ⟨y, hyC, hxy⟩
          rcases hnear y with h | ⟨c', hc', hyc'⟩ | ⟨u', c', hc', hyu', hu'c'⟩
          · exact hyC h
          · obtain ⟨q, hq⟩ := hwC c' hc' c hc
            have := hbr hxu
              (Walk.cons hxy (Walk.cons hyc' (q.append (Walk.cons huc.symm Walk.nil))))
            simp only [Walk.edges_cons, Walk.edges_append, Walk.edges_nil, List.mem_cons,
              List.mem_append, List.not_mem_nil, or_false] at this
            rcases this with h3 | h3 | h3 | h3
            · rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
              · exact hyu h4.symm
              · exact hxne h4
            · rcases Sym2.eq_iff.mp h3 with ⟨h4, -⟩ | ⟨h4, -⟩
              · exact hxne h4
              · exact hx (by rw [h4]; exact hc')
            · exact hnotC q hq hx h3
            · rcases Sym2.eq_iff.mp h3 with ⟨h4, -⟩ | ⟨-, h4⟩
              · exact hx (by rw [h4]; exact hc)
              · exact hu (by rw [h4]; exact hc)
          · obtain ⟨q, hq⟩ := hwC c' hc' c hc
            have := hbr hxu (Walk.cons hxy (Walk.cons hyu' (Walk.cons hu'c'
              (q.append (Walk.cons huc.symm Walk.nil)))))
            simp only [Walk.edges_cons, Walk.edges_append, Walk.edges_nil, List.mem_cons,
              List.mem_append, List.not_mem_nil, or_false] at this
            rcases this with h3 | h3 | h3 | h3 | h3
            · rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
              · exact hyu h4.symm
              · exact hxne h4
            · rcases Sym2.eq_iff.mp h3 with ⟨h4, -⟩ | ⟨-, h4⟩
              · exact hxne h4
              · exact hyu h4.symm
            · rcases Sym2.eq_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
              · exact hu (by rw [h4]; exact hc')
              · exact hx (by rw [h4]; exact hc')
            · exact hnotC q hq hx h3
            · rcases Sym2.eq_iff.mp h3 with ⟨h4, -⟩ | ⟨-, h4⟩
              · exact hx (by rw [h4]; exact hc)
              · exact hu (by rw [h4]; exact hc)
      _ = 1 := card_singleton u
  -- (d) support vertices lie in `S`
  have hSup : ∀ u ℓ, T.Adj u ℓ → T.degree ℓ ≤ 1 → u ∈ S := by
    intro u ℓ h hℓ
    obtain ⟨w, hw, hℓw⟩ := hS ℓ
    have := eq_of_degree_le_one hℓ hℓw h.symm
    rw [← this]
    exact hw
  -- (e) a non-leaf adjacent to `C` but outside it is a support vertex
  have hL1 : ∀ u, u ∉ C → ∀ c ∈ C, T.Adj u c → ¬ T.degree u ≤ 1 → u ∈ S := by
    intro u hu c hc huc hdeg
    obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne
      (by rw [card_neighborFinset_eq_degree]; omega : 1 < #(T.neighborFinset u)) c
    have huy : T.Adj u y := (T.mem_neighborFinset u y).mp hy
    have hyC : y ∉ C := fun hyC => hyc (hA u hu y hyC c hc huy huc)
    have hynadj : ¬ ∃ c' ∈ C, T.Adj y c' := fun ⟨c', hc', hyc'⟩ =>
      hB u y hu hyC c hc c' hc' huc hyc' huy.symm
    exact hSup u y huy (hL2 y hyC hynadj)
  -- (f) each non-leaf outside `S` lies in `C` and yields a leaf in `S`
  set W := univ.filter fun v => ¬ T.degree v ≤ 1
  have hf : ∀ w ∈ W \ S, ∃ y z, T.Adj w y ∧ y ∉ C ∧ T.Adj y z ∧ z ∈ S ∧ T.degree z ≤ 1 := by
    intro w hw
    have hwW : ¬ T.degree w ≤ 1 := (mem_filter.mp (mem_sdiff.mp hw).1).2
    have hwS : w ∉ S := (mem_sdiff.mp hw).2
    have hwC : w ∈ C := by
      by_contra hwC
      by_cases hadj : ∃ c ∈ C, T.Adj w c
      · obtain ⟨c, hc, hwc⟩ := hadj
        exact hwS (hL1 w hwC c hc hwc hwW)
      · exact hwW (hL2 w hwC hadj)
    -- `w` has a neighbour outside `C`
    obtain ⟨y, hwy, hyC⟩ : ∃ y, T.Adj w y ∧ y ∉ C := by
      obtain ⟨y1, hy1⟩ := (T.degree_pos_iff_exists_adj w).mp (by omega)
      obtain ⟨y2, hy2, hne⟩ := Finset.exists_mem_ne
        (by rw [card_neighborFinset_eq_degree]; omega : 1 < #(T.neighborFinset w)) y1
      have hwy2 : T.Adj w y2 := (T.mem_neighborFinset w y2).mp hy2
      by_cases h1 : y1 ∈ C
      · by_cases h2 : y2 ∈ C
        · exfalso
          rcases hC y2 h2 y1 h1 with h | h
          · exact hne h
          · have := hbr hy1 (Walk.cons hwy2 (Walk.cons h Walk.nil))
            simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
              or_false] at this
            rcases this with h3 | h3 <;> rcases Sym2.eq_iff.mp h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
            · exact hne h5.symm
            · exact T.ne_of_adj hwy2 h4
            · exact T.ne_of_adj hwy2 h4
            · exact T.ne_of_adj hy1 h4
        · exact ⟨y2, hwy2, h2⟩
      · exact ⟨y1, hy1, h1⟩
    have hyleaf : ¬ T.degree y ≤ 1 := fun h => hwS (hSup w y hwy h)
    have hyS : y ∈ S := hL1 y hyC w hwC hwy.symm hyleaf
    obtain ⟨z, hzS, hyz⟩ := hS y
    have hzC : z ∉ C := fun hzC => hwS (by rw [hA y hyC w hwC z hzC hwy.symm hyz]; exact hzS)
    have hznadj : ¬ ∃ c ∈ C, T.Adj z c := fun ⟨c, hc, hzc⟩ =>
      hB y z hyC hzC w hwC c hc hwy.symm hzc hyz.symm
    exact ⟨y, z, hwy, hyC, hyz, hzS, hL2 z hzC hznadj⟩
  choose! fy fz hfwy hfyC hfyz hfzS hfz using hf
  have hinj : #(W \ S) ≤ #(S \ W) := by
    apply Finset.card_le_card_of_injOn fz
    · intro w hw
      exact mem_sdiff.mpr ⟨hfzS w hw, fun h => (mem_filter.mp h).2 (hfz w hw)⟩
    · intro w hw w' hw' h
      have hwC : w ∈ C := by
        by_contra hwC
        have hwW : ¬ T.degree w ≤ 1 := (mem_filter.mp (mem_sdiff.mp hw).1).2
        by_cases hadj : ∃ c ∈ C, T.Adj w c
        · obtain ⟨c, hc, hwc⟩ := hadj
          exact (mem_sdiff.mp hw).2 (hL1 w hwC c hc hwc hwW)
        · exact hwW (hL2 w hwC hadj)
      have hwC' : w' ∈ C := by
        by_contra hwC'
        have hwW : ¬ T.degree w' ≤ 1 := (mem_filter.mp (mem_sdiff.mp hw').1).2
        by_cases hadj : ∃ c ∈ C, T.Adj w' c
        · obtain ⟨c, hc, hwc⟩ := hadj
          exact (mem_sdiff.mp hw').2 (hL1 w' hwC' c hc hwc hwW)
        · exact hwW (hL2 w' hwC' hadj)
      have hy : fy w = fy w' := by
        have h1 := hfyz w hw
        have h2 := hfyz w' hw'
        rw [← h] at h2
        exact eq_of_degree_le_one (hfz w hw) h1.symm h2.symm
      have h2 := (hfwy w' hw').symm
      rw [← hy] at h2
      exact hA (fy w) (hfyC w hw) w hwC w' hwC' (hfwy w hw).symm h2
  have e1 := Finset.card_sdiff_add_card_inter W S
  have e2 := Finset.card_sdiff_add_card_inter S W
  rw [inter_comm] at e2
  omega

/-! ### Conjecture 380 -/

/-- In a tree whose vertices lie within distance two of the center, `#non-leaves ≤ |S|`. -/
lemma nonleaves_le_of_center {T : SimpleGraph V} (hT : T.IsTree)
    (hnear : ∀ v, ∃ c ∈ center T, T.dist v c ≤ 2) {S : Finset V} (hS : IsTDS T S) :
    #(univ.filter fun v => ¬ T.degree v ≤ 1) ≤ #S := by
  refine nonleaves_le_of_near hT (fun c hc c' hc' => center_adj hT hc hc') (fun v => ?_) hS
  obtain ⟨c, hc, hvc⟩ := hnear v
  rcases near_cases (hT.connected.preconnected v c) hvc with rfl | h | ⟨u, h1, h2⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨c, hc, h⟩)
  · exact Or.inr (Or.inr ⟨u, c, hc, h1, h2⟩)

/-- Vertices of even degree are non-leaves in a graph without isolated vertices. -/
lemma card_even_le {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    #(univ.filter fun v => Even (T.degree v)) ≤ #(univ.filter fun v => ¬ T.degree v ≤ 1) := by
  apply card_le_card
  intro v hv
  have he := (mem_filter.mp hv).2
  have hp := WOWII377.degree_pos hT hn v
  refine mem_filter.mpr ⟨mem_univ v, fun h => ?_⟩
  have : T.degree v = 1 := by omega
  rw [this] at he
  exact Nat.not_even_one he

/-- The common part of both readings: with `e = ecc(C)` and `e ≥ 2` whenever `e = 2` forces all
vertices to be within distance two of the center, `|D_even| / (e - 1) ≤ γ_t`. -/
lemma bound380 {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 < Fintype.card V) (e : ℕ)
    (he : e = 2 → ∀ v, ∃ c ∈ center T, T.dist v c ≤ 2) :
    (#(univ.filter fun v => Even (T.degree v)) : ℝ) / ((e : ℝ) - 1) ≤ totalDomNum T := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnoiso : ∀ v, ∃ u, T.Adj v u := fun v =>
    (T.degree_pos_iff_exists_adj v).mp (hT.connected.preconnected.degree_pos_of_nontrivial v)
  obtain ⟨S, hS, hScard⟩ := exists_tds_card_eq hnoiso
  rw [← hScard]
  have hE := card_even_le hT (by omega)
  have hW := WOWII367.nonleaves_le hT hS
  set E := #(univ.filter fun v => Even (T.degree v))
  have hS0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
  rcases Nat.lt_or_ge e 2 with h | h
  · have : (e : ℝ) - 1 ≤ 0 := by
      have : (e : ℝ) ≤ 1 := by exact_mod_cast (by omega : e ≤ 1)
      linarith
    exact (div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) this).trans hS0
  rcases Nat.lt_or_ge e 3 with h' | h'
  · have he2 : e = 2 := by omega
    have := nonleaves_le_of_center hT (he he2) hS
    rw [he2]
    norm_num
    exact_mod_cast hE.trans this
  · have hpos : (0 : ℝ) < (e : ℝ) - 1 := by
      have : (3 : ℝ) ≤ e := by exact_mod_cast h'
      linarith
    rw [div_le_iff₀ hpos]
    have h3 : (3 : ℝ) ≤ e := by exact_mod_cast h'
    have hE2 : (E : ℝ) ≤ 2 * #S := by
      have : E ≤ 2 * #S := by omega
      exact_mod_cast this
    nlinarith

/-- **WOWII Conjecture 380**, with `ecc(C)` the eccentricity of the center as a set:
`γ_t(T) ≥ |D_even(T)| / (ecc(C) - 1)` for every tree on more than two vertices. -/
theorem conjecture380 (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 < Fintype.card V) :
    (#(univ.filter fun v => Even (T.degree v)) : ℝ) / ((eccSet T (center T) : ℝ) - 1) ≤
      totalDomNum T := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine bound380 hT hn _ fun he v => ?_
  have h1 : distToSet T v (center T) ≤ 2 :=
    he ▸ Finset.le_sup (f := fun v => distToSet T v (center T)) (mem_univ v)
  obtain ⟨c0, hc0⟩ := center_nonempty T
  have hne : ((fun a => T.dist v a) '' (center T : Set V)).Nonempty :=
    ⟨_, c0, Finset.mem_coe.mpr hc0, rfl⟩
  obtain ⟨c, hc, hcd⟩ := Nat.sInf_mem hne
  refine ⟨c, hc, ?_⟩
  have h' : T.dist v c = distToSet T v (center T) := hcd
  omega

/-- **WOWII Conjecture 380**, with `ecc(C)` the eccentricity of a center vertex (the radius):
`γ_t(T) ≥ |D_even(T)| / (rad(T) - 1)` for every tree on more than two vertices. -/
theorem conjecture380_rad (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 < Fintype.card V) :
    (#(univ.filter fun v => Even (T.degree v)) : ℝ) / ((rad T : ℝ) - 1) ≤ totalDomNum T := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine bound380 hT hn _ fun he v => ?_
  obtain ⟨c0, hc0⟩ := center_nonempty T
  refine ⟨c0, hc0, ?_⟩
  have := dist_le_ecc T c0 v
  rw [(mem_filter.mp hc0).2, he, T.dist_comm] at this
  exact this

/-! ### Conjecture 241 -/

/-- The closed neighbourhood `N[A]` of a set `A`. -/
def closedNbhd (T : SimpleGraph V) (A : Finset V) : Finset V := A ∪ WOWII348.nbhd T A

/-- The subgraph induced by a closed neighbourhood `N[A]` has fewer components than any total
dominating set has vertices. -/
lemma numComp_add_one_le (T : SimpleGraph V) [Nonempty V] (A : Finset V) {S : Finset V}
    (hS : IsTDS T S) : numComp T (closedNbhd T A) + 1 ≤ #S := by
  set K := closedNbhd T A
  set G' := T.induce (K : Set V)
  choose σ hσS hσ using hS
  have hA : ∀ a ∈ A, a ∈ K := fun a ha => mem_union_left _ ha
  have hσK : ∀ a ∈ A, σ a ∈ K := fun a ha => mem_union_right _
    (by simp only [WOWII348.nbhd, mem_filter, mem_univ, true_and]; exact ⟨a, ha, (hσ a).symm⟩)
  -- every component contains `σ a` for some `a ∈ A`
  have hrep : ∀ κ : G'.ConnectedComponent, ∃ a, ∃ ha : a ∈ A,
      G'.connectedComponentMk ⟨σ a, hσK a ha⟩ = κ := by
    intro κ
    obtain ⟨⟨x, hx⟩, rfl⟩ := κ.exists_rep
    have hx' : x ∈ A ∨ ∃ a ∈ A, T.Adj x a := by
      rcases mem_union.mp hx with h | h
      · exact Or.inl h
      · simp only [WOWII348.nbhd, mem_filter, mem_univ, true_and] at h
        exact Or.inr h
    obtain ⟨a, ha, hxa⟩ : ∃ a ∈ A, x = a ∨ T.Adj x a := by
      rcases hx' with h | ⟨a, ha, h⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨a, ha, Or.inr h⟩
    refine ⟨a, ha, ?_⟩
    have h1 : G'.Reachable ⟨σ a, hσK a ha⟩ ⟨a, hA a ha⟩ :=
      Adj.reachable (show T.Adj (σ a) a from (hσ a).symm)
    have h2 : G'.Reachable ⟨a, hA a ha⟩ ⟨x, hx⟩ := by
      rcases hxa with rfl | h
      · exact Reachable.refl _
      · exact Adj.reachable (show T.Adj a x from h.symm)
    exact ConnectedComponent.eq.mpr (h1.trans h2)
  -- a set `D` of vertices of `S ∩ K` meeting every component, with `|D| < |S|`
  obtain ⟨D, hDK, hDS, hDrep⟩ : ∃ D : Finset V, ∃ hDK : (∀ x ∈ D, x ∈ K), #D + 1 ≤ #S ∧
      ∀ κ : G'.ConnectedComponent, ∃ x, ∃ hx : x ∈ D, G'.connectedComponentMk ⟨x, hDK x hx⟩ = κ := by
    by_cases hsub : S ⊆ K
    · obtain ⟨v⟩ := ‹Nonempty V›
      set s0 := σ v
      set s1 := σ s0
      have hs01 : s0 ≠ s1 := T.ne_of_adj (hσ s0)
      refine ⟨S.erase s1, fun x hx => hsub (mem_of_mem_erase hx), ?_, ?_⟩
      · rw [card_erase_of_mem (hσS s0)]
        have : 0 < #S := card_pos.mpr ⟨s0, hσS v⟩
        omega
      · intro κ
        obtain ⟨a, ha, rfl⟩ := hrep κ
        by_cases h : σ a = s1
        · refine ⟨s0, mem_erase.mpr ⟨hs01, hσS v⟩, ?_⟩
          apply ConnectedComponent.eq.mpr
          have : G'.Adj ⟨s0, hsub (hσS v)⟩ ⟨σ a, hσK a ha⟩ := by
            show T.Adj s0 (σ a)
            rw [h]
            exact hσ s0
          exact this.reachable
        · exact ⟨σ a, mem_erase.mpr ⟨h, hσS a⟩, rfl⟩
    · obtain ⟨x, hxS, hxK⟩ := not_subset.mp hsub
      refine ⟨S.filter (· ∈ K), fun y hy => (mem_filter.mp hy).2, ?_, ?_⟩
      · have : #(S.filter (· ∈ K)) < #S :=
          card_lt_card (filter_ssubset.mpr ⟨x, hxS, hxK⟩)
        omega
      · intro κ
        obtain ⟨a, ha, rfl⟩ := hrep κ
        exact ⟨σ a, mem_filter.mpr ⟨hσS a, hσK a ha⟩, rfl⟩
  have : Finite G'.ConnectedComponent := Quot.finite _
  let f : {x // x ∈ D} → G'.ConnectedComponent :=
    fun x => G'.connectedComponentMk ⟨x.1, hDK x.1 x.2⟩
  have hf : Function.Surjective f := by
    intro κ
    obtain ⟨x, hx, h⟩ := hDrep κ
    exact ⟨⟨x, hx⟩, h⟩
  have := Nat.card_le_card_of_surjective f hf
  have hD : Nat.card {x // x ∈ D} = #D := by simp
  rw [hD] at this
  show Nat.card G'.ConnectedComponent + 1 ≤ #S
  omega

/-- In a tree the mean distance between distinct center vertices is at most one. -/
lemma distAvgPairs_center_le {T : SimpleGraph V} (hT : T.IsTree) :
    distAvgPairs T (center T) ≤ 1 := by
  rw [distAvgPairs]
  have hsum : ∑ p ∈ pairs (center T), (T.dist p.1 p.2 : ℝ) = #(pairs (center T)) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [pairs, mem_filter, mem_product] at hp
    rcases center_adj hT hp.1.1 hp.1.2 with h | h
    · exact absurd h hp.2
    · rw [dist_eq_one_iff_adj.mpr h]
  rw [hsum]
  rcases Nat.eq_zero_or_pos #(pairs (center T)) with h | h
  · rw [h]; simp
  · rw [div_self (by exact_mod_cast h.ne')]

/-- **WOWII Conjecture 241**, with `dist_avg(C)` the mean distance between distinct center
vertices: `γ_t(T) ≥ ⌊comp(<N[D_2]>) + dist_avg(C)⌋` for every tree on at least two vertices. -/
theorem conjecture241 (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    ⌊(numComp T (closedNbhd T (WOWII348.D2 T)) : ℝ) + distAvgPairs T (center T)⌋ ≤
      (totalDomNum T : ℤ) := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnoiso : ∀ v, ∃ u, T.Adj v u := fun v =>
    (T.degree_pos_iff_exists_adj v).mp (hT.connected.preconnected.degree_pos_of_nontrivial v)
  obtain ⟨S, hS, hScard⟩ := exists_tds_card_eq hnoiso
  rw [← hScard]
  have h1 := numComp_add_one_le T (WOWII348.D2 T) hS
  have h2 := distAvgPairs_center_le hT
  rw [Int.floor_le_iff]
  have h1' : (numComp T (closedNbhd T (WOWII348.D2 T)) : ℝ) + 1 ≤ #S := by exact_mod_cast h1
  push_cast
  linarith

end WOWII380
