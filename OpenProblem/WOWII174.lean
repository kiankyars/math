import OpenProblem.WOWII178
import OpenProblem.WOWII372
import OpenProblem.WOWII377

/-!
# Written on the Wall II, Conjecture 174 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 174.** If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ n + max_v λ(v) - 1`.

This is also Conjecture 3 of E. DeLaViña and B. Waller, *Spanning trees with many leaves and
average distance*, Electron. J. Combin. 15 (2008), #R33. Here `L_s(G)` is the maximum number of
leaves of a spanning tree, `b(G)` the order of a largest induced bipartite subgraph and
`λ(v) = α(G[N(v)])` (the definitions are those of `OpenProblem/WOWII178.lean`).

The conjecture fails for the following graph on 11 vertices (graph6 `J{Thg_@?G__`,
`not_conjecture174`). The vertex `3` is a cut vertex.

* `A = {0, 1, 2, 4, 5, 6}` is a `3`-sun: a triangle `1, 2, 5` whose edges `12`, `15` and `25` are
  capped by `0`, `4` and `6`. The vertex `3` is adjacent to the caps `0`, `4` and `6`.
* `P = {7, 8, 9, 10}` is a path, and `3 - 7 - 8 - 9 - 10 - 3` is a `5`-cycle.

Then:

* `λ(3) ≥ 5`, since `0, 4, 6, 7, 10` are independent neighbours of `3`.
* `b ≤ 8`. The four triangles of the sun need two vertices removed and the `5`-cycle a third.
* `L_s ≤ 6`. The internal vertices `I` of a spanning tree dominate `G`, and a path in the tree
  between two internal vertices runs through internal vertices only. So `3 ∈ I`. Since `I ∩ A`
  dominates `1, 2, 5` and a single such vertex is never adjacent to `3`, `|I ∩ A| ≥ 2`. In the
  same way `I ∩ P` dominates `8, 9`, so `|I ∩ P| ≥ 2`. Hence `|I| ≥ 5`.

So `L_s + b ≤ 14 < 15 = n + λ(3) - 1`. Gluing more suns and `5`-cycles at the cut vertex makes
the gap arbitrarily large; see `wowii/NOTES.md`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII174

open WOWII178

variable {V : Type*} [Fintype V]

/-- The statement of Conjecture 174, as `n + max λ ≤ L_s + b + 1`. -/
def Conjecture174 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 ≤ Fintype.card V →
    Fintype.card V + maxLocalIndep G ≤ Ls G + b G + 1

/-! ### Internal vertices of a spanning tree -/

/-- An interior vertex of a path has degree at least two. -/
lemma two_le_degree_of_interior {T : SimpleGraph V} {x y z : V} {p : T.Walk x y}
    (hp : p.IsPath) (hz : z ∈ p.support) (hzx : z ≠ x) (hzy : z ≠ y) : 2 ≤ T.degree z := by
  have hspec := p.take_spec hz
  set q := p.takeUntil z hz
  set r := p.dropUntil z hz
  have hq : ¬ q.Nil := Walk.not_nil_of_ne (Ne.symm hzx)
  have hr : ¬ r.Nil := Walk.not_nil_of_ne hzy
  have ha := q.adj_penultimate hq
  have hb := r.adj_snd hr
  have hne : q.penultimate ≠ r.snd := by
    intro h
    have hnd := hp.support_nodup
    rw [← hspec, Walk.support_append, List.nodup_append] at hnd
    have h1 : q.penultimate ∈ q.support := q.getVert_mem_support _
    have h2 : r.snd ∈ r.support.tail := r.snd_mem_tail_support hr
    rw [h] at h1
    exact hnd.2.2 _ h1 _ h2 rfl
  rw [← card_neighborFinset_eq_degree]
  calc 2 = #({q.penultimate, r.snd} : Finset V) := (card_pair hne).symm
    _ ≤ #(T.neighborFinset z) := card_le_card fun w hw => by
        rcases mem_insert.mp hw with rfl | hw
        · exact (T.mem_neighborFinset _ _).mpr ha.symm
        · rw [mem_singleton.mp hw]
          exact (T.mem_neighborFinset _ _).mpr hb

/-- In a tree with at least three vertices, the neighbour of a leaf is not a leaf. -/
lemma degree_ne_one_of_adj_leaf {T : SimpleGraph V} (hT : T.IsTree) (hn : 3 ≤ Fintype.card V)
    {v u : V} (hv : T.degree v = 1) (hvu : T.Adj v u) : T.degree u ≠ 1 := by
  intro hu
  obtain ⟨z, -, hz⟩ := exists_mem_notMem_of_card_lt_card
    (show #({u, v} : Finset V) < #(univ : Finset V) by
      rw [card_univ]; exact (card_le_two).trans_lt (by omega))
  refine WOWII372.not_reachable_of_closed ({u, v} : Finset V) (by simp) (by simpa using hz) ?_
    (hT.connected.preconnected v z)
  intro a w haw ha
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl
  · exact Or.inr (WOWII377.eq_of_degree_le_one hu.le haw hvu.symm)
  · exact Or.inl (WOWII377.eq_of_degree_le_one hv.le haw hvu)

/-- In a tree with at least three vertices, the internal vertices dominate. -/
lemma internal_dom {T : SimpleGraph V} (hT : T.IsTree) (hn : 3 ≤ Fintype.card V) (v : V) :
    ¬ T.degree v = 1 ∨ ∃ u, ¬ T.degree u = 1 ∧ T.Adj v u := by
  by_cases hv : T.degree v = 1
  · right
    have : 0 < #(T.neighborFinset v) := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨u, hu⟩ := card_pos.mp this
    have hvu := (T.mem_neighborFinset v u).mp hu
    exact ⟨u, degree_ne_one_of_adj_leaf hT hn hv hvu, hvu⟩
  · exact Or.inl hv

/-- A path in a tree between two internal vertices runs through internal vertices only, so it
crosses the boundary of any set separating them along an edge between internal vertices. -/
lemma exists_cross {T : SimpleGraph V} (hT : T.IsTree) (X : Set V) {x y : V}
    (hx : ¬ T.degree x = 1) (hy : ¬ T.degree y = 1) (hxX : x ∈ X) (hyX : y ∉ X) :
    ∃ s t, ¬ T.degree s = 1 ∧ s ∈ X ∧ ¬ T.degree t = 1 ∧ t ∉ X ∧ T.Adj s t := by
  obtain ⟨q⟩ := hT.connected.preconnected x y
  have hp := q.bypass_isPath
  have hsupp : ∀ z ∈ q.bypass.support, ¬ T.degree z = 1 := by
    intro z hz
    by_cases hzx : z = x
    · rw [hzx]; exact hx
    by_cases hzy : z = y
    · rw [hzy]; exact hy
    have := two_le_degree_of_interior hp hz hzx hzy
    omega
  obtain ⟨d, hd, hd1, hd2⟩ := q.bypass.exists_boundary_dart X hxX hyX
  exact ⟨d.fst, d.snd, hsupp _ (q.bypass.dart_fst_mem_support_of_mem_darts hd), hd1,
    hsupp _ (q.bypass.dart_snd_mem_support_of_mem_darts hd), hd2, d.adj⟩

/-! ### The counterexample -/

/-- The edges of the counterexample. -/
def E : List (Fin 11 × Fin 11) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (1, 5), (2, 5), (2, 6), (3, 4), (3, 6), (3, 7),
    (3, 10), (4, 5), (5, 6), (7, 8), (8, 9), (9, 10)]

/-- Adjacency in the counterexample. -/
def adjB (a b : Fin 11) : Bool := E.contains (a, b) || E.contains (b, a)

/-- The counterexample, with graph6 code `J{Thg_@?G__`. -/
def G : SimpleGraph (Fin 11) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 11} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 11, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨3, fun w => ?_⟩
  by_cases hw : w = 3
  · rw [hw]
  by_cases h1 : adjB 3 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 3 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

/-! ### `λ(3) ≥ 5` -/

lemma G_maxLocalIndep : 5 ≤ maxLocalIndep G := by
  refine le_trans ?_ (le_sup (f := localIndep G) (mem_univ 3))
  unfold localIndep
  set N := G.neighborSet 3
  set t : Finset N := ({0, 4, 6, 7, 10} : Finset (Fin 11)).subtype (· ∈ N)
  have ht : #t = 5 := by
    rw [card_subtype, filter_true_of_mem]
    · rfl
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      refine (G.mem_neighborSet 3 v).mpr ?_
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact G_adj.mpr (by decide)
  have hind : (G.induce N).IsIndepSet (t : Set N) := by
    intro a ha c hc _ hac
    have key : ∀ x ∈ ([0, 4, 6, 7, 10] : List (Fin 11)), ∀ y ∈ ([0, 4, 6, 7, 10] : List (Fin 11)),
        adjB x y = false := by decide
    have ha' : a.1 ∈ ({0, 4, 6, 7, 10} : Finset (Fin 11)) := (mem_subtype.mp ha)
    have hc' : c.1 ∈ ({0, 4, 6, 7, 10} : Finset (Fin 11)) := (mem_subtype.mp hc)
    have hac' : adjB a.1 c.1 = true := G_adj.mp (by simpa [comap_adj] using hac)
    rw [key a.1 (by simpa using ha') c.1 (by simpa using hc')] at hac'
    exact absurd hac' (by decide)
  calc 5 = #t := ht.symm
    _ ≤ _ := hind.card_le_indepNum

/-! ### `b ≤ 8` -/

lemma G_b : b G ≤ 8 := by
  refine csSup_le' fun k hk => ?_
  obtain ⟨s, hs, rfl⟩ := hk
  obtain ⟨C⟩ := hs
  have col : ∀ x y : Fin 11, (hx : x ∈ s) → (hy : y ∈ s) → adjB x y = true →
      C ⟨x, hx⟩ ≠ C ⟨y, hy⟩ := fun x y hx hy hxy =>
    C.valid (by simpa [comap_adj] using G_adj.mpr hxy)
  have k3 : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a ≠ c → False := by decide
  have k5 : ∀ a b c d e : Fin 2, a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a → False := by
    intro a b c d e
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> simp
  -- each odd cycle has a vertex outside `s`
  have tri : ∀ x y z : Fin 11, adjB x y = true → adjB y z = true → adjB x z = true →
      ∃ w ∈ [x, y, z], w ∉ s := by
    intro x y z h1 h2 h3
    by_contra hall
    push Not at hall
    have hx := hall x (by simp)
    have hy := hall y (by simp)
    have hz := hall z (by simp)
    exact k3 _ _ _ (col x y hx hy h1) (col y z hy hz h2) (col x z hx hz h3)
  have pent : ∃ w ∈ ([3, 7, 8, 9, 10] : List (Fin 11)), w ∉ s := by
    by_contra hall
    push Not at hall
    have h3 := hall 3 (by simp)
    have h7 := hall 7 (by simp)
    have h8 := hall 8 (by simp)
    have h9 := hall 9 (by simp)
    have h10 := hall 10 (by simp)
    exact k5 _ _ _ _ _ (col 3 7 h3 h7 (by decide)) (col 7 8 h7 h8 (by decide))
      (col 8 9 h8 h9 (by decide)) (col 9 10 h9 h10 (by decide)) (col 10 3 h10 h3 (by decide))
  obtain ⟨w1, hw1, hs1⟩ := tri 1 2 5 (by decide) (by decide) (by decide)
  obtain ⟨w5, hw5, hs5⟩ := pent
  -- two distinct vertices of the sun and one of the pentagon lie outside `s`
  have three : ∃ x y z : Fin 11, x ∉ s ∧ y ∉ s ∧ z ∉ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw5
    rcases hw1 with rfl | rfl | rfl
    · obtain ⟨w4, hw4, hs4⟩ := tri 2 5 6 (by decide) (by decide) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw4
      refine ⟨1, w4, w5, hs1, hs4, hs5, ?_⟩
      rcases hw4 with rfl | rfl | rfl <;> rcases hw5 with rfl | rfl | rfl | rfl | rfl <;> decide
    · obtain ⟨w3, hw3, hs3⟩ := tri 1 4 5 (by decide) (by decide) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw3
      refine ⟨2, w3, w5, hs1, hs3, hs5, ?_⟩
      rcases hw3 with rfl | rfl | rfl <;> rcases hw5 with rfl | rfl | rfl | rfl | rfl <;> decide
    · obtain ⟨w2, hw2, hs2⟩ := tri 0 1 2 (by decide) (by decide) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw2
      refine ⟨5, w2, w5, hs1, hs2, hs5, ?_⟩
      rcases hw2 with rfl | rfl | rfl <;> rcases hw5 with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := three
  have hsub : ({x, y, z} : Finset (Fin 11)) ⊆ sᶜ := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rw [mem_compl]
    rcases hw with rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  rw [card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩, card_compl, Fintype.card_fin] at this
  omega

/-! ### `L_s ≤ 6` -/

/-- The part `A` (the sun). -/
def inA (v : Fin 11) : Bool := ([0, 1, 2, 4, 5, 6] : List (Fin 11)).contains v

/-- The part `P` (the path). -/
def inP (v : Fin 11) : Bool := ([7, 8, 9, 10] : List (Fin 11)).contains v

/-- A dominating set of `G` that is connected across the cuts at `3` has at least five
vertices. -/
lemma five_le {I : Finset (Fin 11)} (hdom : ∀ v, v ∈ I ∨ ∃ u ∈ I, adjB v u = true)
    (hcut : ∀ X : Fin 11 → Bool, ∀ x ∈ I, X x = true → ∀ y ∈ I, X y = false →
      ∃ s ∈ I, X s = true ∧ ∃ t ∈ I, X t = false ∧ adjB s t = true) :
    5 ≤ #I := by
  have fA : ∀ s t : Fin 11, inA s = true → inA t = false → adjB s t = true → t = 3 := by decide
  have fP : ∀ s t : Fin 11, inP s = true → inP t = false → adjB s t = true → t = 3 := by decide
  -- a dominator of `k`
  have dom : ∀ k : Fin 11, ∃ u ∈ I, u = k ∨ adjB k u = true := by
    intro k
    rcases hdom k with h | ⟨u, hu, h⟩
    · exact ⟨k, h, Or.inl rfl⟩
    · exact ⟨u, hu, Or.inr h⟩
  -- `3 ∈ I`
  have h3 : (3 : Fin 11) ∈ I := by
    obtain ⟨u8, hu8, e8⟩ := dom 8
    obtain ⟨u1, hu1, e1⟩ := dom 1
    have a8 : inA u8 = false :=
      (by decide : ∀ u : Fin 11, (u = 8 ∨ adjB 8 u = true) → inA u = false) u8 e8
    have a1 : inA u1 = true :=
      (by decide : ∀ u : Fin 11, (u = 1 ∨ adjB 1 u = true) → inA u = true) u1 e1
    obtain ⟨s, -, hsA, t, ht, htA, hst⟩ := hcut inA u1 hu1 a1 u8 hu8 a8
    rw [← fA s t hsA htA hst]
    exact ht
  -- `|I ∩ A| ≥ 2`
  have hA : 2 ≤ #(I.filter fun v => inA v = true) := by
    by_contra hlt
    have hle := card_le_one.mp (show #(I.filter fun v => inA v = true) ≤ 1 by omega)
    obtain ⟨d1, hd1, e1⟩ := dom 1
    obtain ⟨d2, hd2, e2⟩ := dom 2
    obtain ⟨d5, hd5, e5⟩ := dom 5
    have a1 := (by decide : ∀ u : Fin 11, (u = 1 ∨ adjB 1 u = true) → inA u = true) d1 e1
    have a2 := (by decide : ∀ u : Fin 11, (u = 2 ∨ adjB 2 u = true) → inA u = true) d2 e2
    have a5 := (by decide : ∀ u : Fin 11, (u = 5 ∨ adjB 5 u = true) → inA u = true) d5 e5
    have m1 : d1 ∈ I.filter fun v => inA v = true := mem_filter.mpr ⟨hd1, a1⟩
    have h12 : d2 = d1 := hle d2 (mem_filter.mpr ⟨hd2, a2⟩) d1 m1
    have h15 : d5 = d1 := hle d5 (mem_filter.mpr ⟨hd5, a5⟩) d1 m1
    rw [h12] at e2
    rw [h15] at e5
    obtain ⟨s, hs, hsA, t, ht, htA, hst⟩ := hcut inA d1 hd1 a1 3 h3 (by decide)
    have hs1 : s = d1 := hle s (mem_filter.mpr ⟨hs, hsA⟩) d1 m1
    have ht3 := fA s t hsA htA hst
    rw [hs1, ht3] at hst
    have key : ∀ a : Fin 11, (a = 1 ∨ adjB 1 a = true) → (a = 2 ∨ adjB 2 a = true) →
        (a = 5 ∨ adjB 5 a = true) → adjB a 3 = false := by decide
    rw [key d1 e1 e2 e5] at hst
    exact absurd hst (by decide)
  -- `|I ∩ P| ≥ 2`
  have hP : 2 ≤ #(I.filter fun v => inP v = true) := by
    by_contra hlt
    have hle := card_le_one.mp (show #(I.filter fun v => inP v = true) ≤ 1 by omega)
    obtain ⟨d8, hd8, e8⟩ := dom 8
    obtain ⟨d9, hd9, e9⟩ := dom 9
    have a8 := (by decide : ∀ u : Fin 11, (u = 8 ∨ adjB 8 u = true) → inP u = true) d8 e8
    have a9 := (by decide : ∀ u : Fin 11, (u = 9 ∨ adjB 9 u = true) → inP u = true) d9 e9
    have m8 : d8 ∈ I.filter fun v => inP v = true := mem_filter.mpr ⟨hd8, a8⟩
    have h98 : d9 = d8 := hle d9 (mem_filter.mpr ⟨hd9, a9⟩) d8 m8
    rw [h98] at e9
    obtain ⟨s, hs, hsP, t, ht, htP, hst⟩ := hcut inP d8 hd8 a8 3 h3 (by decide)
    have hs8 : s = d8 := hle s (mem_filter.mpr ⟨hs, hsP⟩) d8 m8
    have ht3 := fP s t hsP htP hst
    rw [hs8, ht3] at hst
    have key : ∀ a : Fin 11, (a = 8 ∨ adjB 8 a = true) → (a = 9 ∨ adjB 9 a = true) →
        adjB a 3 = false := by decide
    rw [key d8 e8 e9] at hst
    exact absurd hst (by decide)
  -- count
  have hsplit := card_filter_add_card_filter_not (s := I) (p := fun v => inA v = true)
  have hsub : insert 3 (I.filter fun v => inP v = true) ⊆ I.filter fun v => ¬ inA v = true := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_filter.mpr ⟨h3, by decide⟩
    · obtain ⟨hvI, hvP⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨hvI, (by decide : ∀ v : Fin 11, inP v = true → ¬ inA v = true) v hvP⟩
  have h3P : (3 : Fin 11) ∉ I.filter fun v => inP v = true := by
    intro h
    exact absurd (mem_filter.mp h).2 (by decide)
  have := card_le_card hsub
  rw [card_insert_of_notMem h3P] at this
  omega

lemma G_Ls : Ls G ≤ 6 := by
  refine csSup_le' fun k hk => ?_
  obtain ⟨T, hTG, hT, rfl⟩ := hk
  have hn : 3 ≤ Fintype.card (Fin 11) := by simp
  set L := univ.filter fun v => T.degree v = 1 with hL
  have hI : ∀ v, v ∈ Lᶜ ↔ ¬ T.degree v = 1 := fun v => by simp [hL]
  have hdom : ∀ v, v ∈ Lᶜ ∨ ∃ u ∈ Lᶜ, adjB v u = true := by
    intro v
    rcases internal_dom hT hn v with h | ⟨u, hu, hvu⟩
    · exact Or.inl ((hI v).mpr h)
    · exact Or.inr ⟨u, (hI u).mpr hu, G_adj.mp (hTG hvu)⟩
  have hcut : ∀ X : Fin 11 → Bool, ∀ x ∈ Lᶜ, X x = true → ∀ y ∈ Lᶜ, X y = false →
      ∃ s ∈ Lᶜ, X s = true ∧ ∃ t ∈ Lᶜ, X t = false ∧ adjB s t = true := by
    intro X x hx hxX y hy hyX
    obtain ⟨s, t, hs, hsX, ht, htX, hst⟩ := exists_cross hT {v | X v = true}
      ((hI x).mp hx) ((hI y).mp hy) hxX (by simp [hyX])
    refine ⟨s, (hI s).mpr hs, hsX, t, (hI t).mpr ht, ?_, G_adj.mp (hTG hst)⟩
    simpa using htX
  have h5 := five_le hdom hcut
  rw [card_compl, Fintype.card_fin] at h5
  have : numLeaves T = #L := rfl
  omega

/-- **WOWII Conjecture 174 (DeLaViña–Waller, Conjecture 3) is false.** -/
theorem not_conjecture174 : ¬ Conjecture174 := by
  intro h
  have h1 := h (Fin 11) G G_connected (by simp)
  have := G_Ls
  have := G_b
  have := G_maxLocalIndep
  rw [Fintype.card_fin] at h1
  omega

end WOWII174
