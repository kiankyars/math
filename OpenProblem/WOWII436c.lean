import OpenProblem.WOWII399b
import OpenProblem.WOWII425e
import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 436c

E. DeLaViña's *Written on the Wall II* lists as open, with partial results:

> **Conjecture 436c.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ k · WP(Ḡ) + Δ(G[D])`, where `Δ(G[D])` is the maximum degree of the subgraph induced by
> the neighbor dominators and `k` is the `k`th step for a zero in the Havel–Hakimi process.

Here `α_2` is the 2-independence number, `WP` the Welsh–Powell number, and `v` is a neighbor
dominator if `N[u] ⊆ N[v]` for some `u ≠ v`. As in formal-conjectures (Conjecture 291), `k` is the
first step of the Havel–Hakimi process on the degree sequence at which a zero appears.

DeLaViña and Pepper proved `α_2 ≤ WP(Ḡ) + 1`. WOWII notes that this leaves only the case
`k = 1` with `D` independent, where `α_2 ≤ WP(Ḡ)` must be shown. We settle that case
(`twoIndepNum_le_WP`) and prove the conjecture (`conjecture436c`).

**The case `k = 1`, `D` independent.** If `k = 1`, at most `Δ` vertices have degree at least two.
Let `S` be a maximum 2-independent set, `s = |S|`, and call a vertex *small* if its degree is at
most `n - s`. It suffices to find `s` small vertices, because a small vertex has degree at least
`s - 1` in `Ḡ`.

* If every vertex of `S` is small, we are done.
* Otherwise some `x ∈ S` has degree `n - s + 1`. Then `x` is adjacent to every vertex outside `S`
  and to exactly one vertex `y ∈ S`, and `N[y] ⊆ N[x]`. So `x ∈ D`, and since `D` is independent,
  no vertex outside `S` lies in `D`.
* A vertex `v₁` of maximum degree has a leaf neighbour, so `v₁` is a neighbor dominator and lies
  in `S`. Hence `Δ = n - s + 1`, and there are at least `n - Δ = s - 1` leaves, all small.
* If there are only `s - 1` leaves, every non-leaf of degree `Δ` is a support vertex, so lies in
  `D`. Since `D` is independent and `v₁` has a non-leaf neighbour, some non-leaf is small. That
  gives `s` small vertices.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII436c

open WOWII399b WOWII425e WOWII449

variable {V : Type*} [Fintype V]

/-! ### Definitions -/

/-- One step of the Havel–Hakimi process on a nonincreasing list. -/
def hhStep : List ℕ → List ℕ
  | [] => []
  | d :: r => ((r.take d).map (· - 1) ++ r.drop d).insertionSort (· ≥ ·)

/-- The degree sequence in nonincreasing order. -/
def degSeq (G : SimpleGraph V) : List ℕ := (univ.val.map fun v => G.degree v).sort (· ≥ ·)

/-- The list after `i` Havel–Hakimi steps. -/
def hhSeq (G : SimpleGraph V) (i : ℕ) : List ℕ := hhStep^[i] (degSeq G)

/-- The first step of the Havel–Hakimi process at which a zero appears (or the list is used up). -/
def hhZeroStep (G : SimpleGraph V) : ℕ := sInf {i | 0 ∈ hhSeq G i ∨ hhSeq G i = []}

/-- The maximum degree of `G[D]`. -/
def maxDegIn (G : SimpleGraph V) (D : Finset V) : ℕ := D.sup fun v => #(D.filter (G.Adj v))

/-- The statement of Conjecture 436c. -/
def Conjecture436c : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    twoIndepNum G ≤ hhZeroStep G * WP Gᶜ + maxDegIn G (nbrDom G)

/-! ### Basic lemmas -/

/-- At least `k` vertices of degree at least `k - 1` give `k ≤ WP H`. -/
lemma le_WP (H : SimpleGraph V) (T : Finset V) (k : ℕ) (hT : k ≤ #T)
    (h : ∀ v ∈ T, k ≤ H.degree v + 1) : k ≤ WP H := by
  have hbdd : BddAbove {k | k ≤ #(univ.filter fun v => k ≤ H.degree v + 1)} :=
    ⟨Fintype.card V, fun k hk => le_trans hk (card_le_univ _)⟩
  refine le_csSup hbdd (le_trans hT (card_le_card fun v hv => ?_))
  simp only [mem_filter, mem_univ, true_and]
  exact h v hv

/-- Degrees in a graph and its complement add up to `n - 1`. -/
lemma degree_add_degree_of_compl (G H : SimpleGraph V)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ ¬ G.Adj x y) (v : V) :
    H.degree v + G.degree v + 1 = Fintype.card V := by
  rw [degree_eq_card_filter, degree_eq_card_filter]
  have hdisj : Disjoint (univ.filter (H.Adj v)) (univ.filter (G.Adj v)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [mem_filter, mem_univ, true_and] at hu hu'
    exact ((hH v u).mp hu).2 hu'
  have hunion : univ.filter (H.Adj v) ∪ univ.filter (G.Adj v) = univ.erase v := by
    ext u
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_erase, and_true, hH]
    constructor
    · rintro (h | h)
      · exact h.1.symm
      · exact (G.ne_of_adj h).symm
    · intro hu
      by_cases h : G.Adj v u
      · exact Or.inr h
      · exact Or.inl ⟨Ne.symm hu, h⟩
  rw [← card_union_of_disjoint hdisj, hunion, card_erase_of_mem (mem_univ v), card_univ]
  have := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

omit [Fintype V] in
/-- A walk starting in a set closed under adjacency stays in it. -/
lemma mem_of_closed {G : SimpleGraph V} {A : Set V} (hA : ∀ u v, u ∈ A → G.Adj u v → v ∈ A) :
    ∀ {u v : V} (_ : G.Walk u v), u ∈ A → v ∈ A
  | _, _, .nil, h => h
  | _, _, .cons hadj p, h => mem_of_closed hA p (hA _ _ h hadj)

/-- A vertex of degree at most one has at most one neighbour. -/
lemma adj_unique {G : SimpleGraph V} {v w x : V} (hdeg : G.degree v ≤ 1) (hw : G.Adj v w)
    (hx : G.Adj v x) : x = w := by
  by_contra hxw
  have hsub : ({w, x} : Finset V) ⊆ G.neighborFinset v := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl <;> simpa
  have := card_le_card hsub
  rw [card_pair (Ne.symm hxw), card_neighborFinset_eq_degree] at this
  omega

/-- `α_2(G) ≤ WP(Ḡ) + 1` (DeLaViña–Pepper). -/
theorem twoIndepNum_le_WP_add_one (G : SimpleGraph V) : twoIndepNum G ≤ WP Gᶜ + 1 := by
  obtain ⟨S, hS, hcard⟩ := exists_twoIndep G
  rw [← hcard]
  by_cases h1 : #S ≤ 1
  · omega
  have := le_WP Gᶜ S (#S - 1) (by omega) fun x hx => by
    rw [degree_eq_card_filter]
    have h1 := hS x hx
    have h3 : #(S.erase x) - #(S.filter (G.Adj x)) ≤ #((S.erase x) \ S.filter (G.Adj x)) :=
      le_card_sdiff _ _
    rw [card_erase_of_mem hx] at h3
    refine le_trans ?_ (Nat.add_le_add_right
      (card_le_card (s := (S.erase x) \ S.filter (G.Adj x)) fun y hy => ?_) 1)
    · omega
    · simp only [mem_sdiff, mem_erase, mem_filter, not_and] at hy
      simp only [mem_filter, mem_univ, true_and, compl_adj]
      exact ⟨Ne.symm hy.1.1, hy.2 hy.1.2⟩
  omega

/-- Splitting the neighbourhood of `x` along `S`. -/
lemma degree_le_split (G : SimpleGraph V) (S : Finset V) (x : V) :
    G.degree x ≤ #(S.filter (G.Adj x)) + #(Sᶜ.filter (G.Adj x)) := by
  rw [degree_eq_card_filter]
  refine le_trans (card_le_card fun y hy => ?_) (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and] at hy
  by_cases hyS : y ∈ S
  · exact mem_union_left _ (mem_filter.mpr ⟨hyS, hy⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr hyS, hy⟩)

/-- **The remaining case of Conjecture 436c.** If at most `Δ` vertices have degree at least two
and the neighbor dominators are independent, then `α_2(G) ≤ WP(Ḡ)`. -/
theorem twoIndepNum_le_WP (G : SimpleGraph V) (hG : G.Connected) (hn : 3 ≤ Fintype.card V)
    (hH : #(univ.filter fun v => 2 ≤ G.degree v) ≤ G.maxDegree)
    (hD : ∀ x ∈ nbrDom G, ∀ y ∈ nbrDom G, ¬ G.Adj x y) : twoIndepNum G ≤ WP Gᶜ := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos : ∀ v, 0 < G.degree v := fun v => hG.preconnected.degree_pos_of_nontrivial v
  obtain ⟨S, hS, hcard⟩ := exists_twoIndep G
  rw [← hcard]
  set n := Fintype.card V with hn_def
  set s := #S with hs_def
  set Hs := univ.filter fun v => 2 ≤ G.degree v with hHs
  -- supports of leaves are neighbor dominators
  have hsupp : ∀ ℓ p, G.degree ℓ ≤ 1 → G.Adj ℓ p → p ∈ nbrDom G := by
    intro ℓ p hℓ hℓp
    simp only [nbrDom, mem_filter, mem_univ, true_and]
    refine ⟨ℓ, G.ne_of_adj hℓp, fun w hw => ?_⟩
    rcases hw with rfl | hw
    · exact Or.inr hℓp.symm
    · exact Or.inl (adj_unique hℓ hℓp hw)
  -- some vertex has degree at least two
  have hex2 : ∃ v, 2 ≤ G.degree v := by
    by_contra h
    push Not at h
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    obtain ⟨w, hw⟩ : ∃ w, G.Adj v w := by
      have := hpos v
      rw [← card_neighborFinset_eq_degree] at this
      obtain ⟨w, hw⟩ := card_pos.mp this
      exact ⟨w, (mem_neighborFinset _ _ _).mp hw⟩
    have hclosed : ∀ a b, a ∈ ({v, w} : Set V) → G.Adj a b → b ∈ ({v, w} : Set V) := by
      intro a b ha hab
      rcases ha with rfl | rfl
      · exact Or.inr (adj_unique (by have := h a; omega) hw hab)
      · exact Or.inl (adj_unique (by have := h a; omega) hw.symm hab)
    have hall : ∀ u, u ∈ ({v, w} : Set V) := fun u =>
      mem_of_closed hclosed (hG.preconnected v u).some (Or.inl rfl)
    have hsub : (univ : Finset V) ⊆ {v, w} := fun u _ => by
      rcases hall u with h | h
      · rw [h]
        exact mem_insert_self _ _
      · rw [Set.mem_singleton_iff.mp h]
        simp
    have := card_le_card hsub
    rw [card_univ] at this
    have := card_insert_le v ({w} : Finset V)
    simp at this
    omega
  -- `S` is not everything
  have hsn : s < n := by
    obtain ⟨v, hv⟩ := hex2
    by_contra hge
    have hSu : S = univ := eq_univ_of_card S (le_antisymm (card_le_univ S) (by omega))
    have := hS v (by simp [hSu])
    rw [hSu, ← degree_eq_card_filter] at this
    omega
  -- it suffices to find `s` small vertices
  set Small := univ.filter fun v => G.degree v + s ≤ n with hSmall
  suffices hsmall : s ≤ #Small by
    refine le_WP Gᶜ Small s hsmall fun v hv => ?_
    simp only [hSmall, mem_filter, mem_univ, true_and] at hv
    have := degree_add_degree_of_compl G Gᶜ (fun x y => compl_adj G x y) v
    omega
  by_cases hbig : ∀ x ∈ S, G.degree x + s ≤ n
  · exact card_le_card fun x hx => by simp [hSmall, hbig x hx]
  push Not at hbig
  obtain ⟨x, hxS, hxbig⟩ := hbig
  have hScard : #Sᶜ = n - s := by rw [card_compl]
  -- `x` is adjacent to everything outside `S` and to exactly one vertex of `S`
  have hsplit := degree_le_split G S x
  have hx1 := hS x hxS
  have hScx : #(Sᶜ.filter (G.Adj x)) ≤ #Sᶜ := card_filter_le _ _
  have hall : ∀ z ∉ S, G.Adj x z := by
    have heq : Sᶜ.filter (G.Adj x) = Sᶜ :=
      eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    intro z hz
    have : z ∈ Sᶜ.filter (G.Adj x) := by
      rw [heq]
      exact mem_compl.mpr hz
    exact (mem_filter.mp this).2
  obtain ⟨y, hy⟩ : ∃ y, S.filter (G.Adj x) = {y} := card_eq_one.mp (by omega)
  have hyS : y ∈ S := (mem_filter.mp (hy ▸ mem_singleton_self y)).1
  have hxy : G.Adj x y := (mem_filter.mp (hy ▸ mem_singleton_self y)).2
  -- `x` dominates `y`
  have hxD : x ∈ nbrDom G := by
    simp only [nbrDom, mem_filter, mem_univ, true_and]
    refine ⟨y, (G.ne_of_adj hxy).symm, fun w hw => ?_⟩
    rcases hw with rfl | hyw
    · exact Or.inr hxy
    · by_cases hwS : w ∈ S
      · left
        have h1 := hS y hyS
        rw [card_le_one] at h1
        exact h1 w (mem_filter.mpr ⟨hwS, hyw⟩) x (mem_filter.mpr ⟨hxS, hxy.symm⟩)
      · exact Or.inr (hall w hwS)
  have hScD : ∀ z ∉ S, z ∉ nbrDom G := fun z hz hzD => hD x hxD z hzD (hall z hz)
  -- a vertex with at least `|Hs|` neighbours has a leaf neighbour
  have has_leaf : ∀ z ∈ Hs, #Hs ≤ G.degree z → ∃ ℓ, G.Adj z ℓ ∧ G.degree ℓ ≤ 1 := by
    intro z hz hzd
    by_contra h
    push Not at h
    have hsub : univ.filter (G.Adj z) ⊆ Hs.erase z := by
      intro u hu
      simp only [mem_filter, mem_univ, true_and] at hu
      simp only [hHs, mem_erase, mem_filter, mem_univ, true_and]
      exact ⟨(G.ne_of_adj hu).symm, h u hu⟩
    have := card_le_card hsub
    rw [← degree_eq_card_filter, card_erase_of_mem hz] at this
    have := card_pos.mpr ⟨z, hz⟩
    omega
  -- the maximum degree vertex
  obtain ⟨v1, hv1⟩ := G.exists_maximal_degree_vertex
  have hv1Hs : v1 ∈ Hs := by
    obtain ⟨v, hv⟩ := hex2
    simp only [hHs, mem_filter, mem_univ, true_and]
    have := G.degree_le_maxDegree v
    omega
  obtain ⟨ℓ1, hv1ℓ, hℓ1⟩ := has_leaf v1 hv1Hs (by omega)
  have hv1D : v1 ∈ nbrDom G := hsupp ℓ1 v1 hℓ1 hv1ℓ.symm
  have hv1S : v1 ∈ S := by
    by_contra h
    exact hScD v1 h hv1D
  have hsplit1 := degree_le_split G S v1
  have h11 := hS v1 hv1S
  have hSc1 : #(Sᶜ.filter (G.Adj v1)) ≤ #Sᶜ := card_filter_le _ _
  have hxle := G.degree_le_maxDegree x
  -- so `Δ = n - s + 1`
  have hΔ : G.maxDegree + s = n + 1 := by omega
  -- the leaves are small
  set Lv := univ.filter fun v => G.degree v ≤ 1 with hLv
  have hLvc : Lv = Hsᶜ := by
    ext v
    simp only [hLv, hHs, mem_filter, mem_univ, true_and, mem_compl]
    omega
  have hLcard : #Lv + #Hs = n := by
    rw [hLvc, card_compl]
    have := card_le_univ Hs
    omega
  have hLsmall : Lv ⊆ Small := by
    intro v hv
    simp only [hLv, hSmall, mem_filter, mem_univ, true_and] at hv ⊢
    omega
  by_cases hL : s ≤ #Lv
  · exact hL.trans (card_le_card hLsmall)
  push Not at hL
  -- some non-leaf is small
  obtain ⟨z, hzHs, hzsmall⟩ : ∃ z ∈ Hs, G.degree z + s ≤ n := by
    by_contra hno
    push Not at hno
    -- `v1` has a non-leaf neighbour
    obtain ⟨z', hv1z', hz'⟩ : ∃ z', G.Adj v1 z' ∧ 2 ≤ G.degree z' := by
      by_contra hno'
      push Not at hno'
      have hclosed : ∀ a b, a ∈ ({v1} ∪ {w | G.Adj v1 w} : Set V) → G.Adj a b →
          b ∈ ({v1} ∪ {w | G.Adj v1 w} : Set V) := by
        intro a b ha hab
        rcases ha with rfl | ha
        · exact Or.inr hab
        · left
          exact adj_unique (by have := hno' a ha; omega) (ha : G.Adj v1 a).symm hab
      have hHs1 : Hs ⊆ {v1} := by
        intro u hu
        have hmem := mem_of_closed hclosed (hG.preconnected v1 u).some (Or.inl rfl)
        rcases hmem with h | h
        · simpa using h
        · have := hno' u h
          simp only [hHs, mem_filter, mem_univ, true_and] at hu
          omega
      have := card_le_card hHs1
      simp at this
      omega
    have hz'Hs : z' ∈ Hs := by simp [hHs, hz']
    obtain ⟨ℓ', hz'ℓ', hℓ'⟩ := has_leaf z' hz'Hs (by have := hno z' hz'Hs; omega)
    exact hD v1 hv1D z' (hsupp ℓ' z' hℓ' hz'ℓ'.symm) hv1z'
  have hzL : z ∉ Lv := by
    simp only [hHs, mem_filter, mem_univ, true_and] at hzHs
    simp only [hLv, mem_filter, mem_univ, true_and]
    omega
  have hsub : insert z Lv ⊆ Small := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp [hSmall, hzsmall]
    · exact hLsmall hv
  have := card_le_card hsub
  rw [card_insert_of_notMem hzL] at this
  omega

/-! ### The Havel–Hakimi step `k` -/

lemma length_hhStep (l : List ℕ) : (hhStep l).length = l.length - 1 := by
  cases l with
  | nil => rfl
  | cons d r =>
    simp only [hhStep, (List.perm_insertionSort _ _).length_eq, List.length_append,
      List.length_map, List.length_take, List.length_drop, List.length_cons]
    omega

lemma length_degSeq (G : SimpleGraph V) : (degSeq G).length = Fintype.card V := by
  simp [degSeq, Multiset.length_sort]

lemma hhSeq_succ (G : SimpleGraph V) (i : ℕ) : hhSeq G (i + 1) = hhStep (hhSeq G i) :=
  Function.iterate_succ_apply' _ _ _

lemma length_hhSeq (G : SimpleGraph V) (i : ℕ) : (hhSeq G i).length = Fintype.card V - i := by
  induction i with
  | zero => simp [hhSeq, length_degSeq]
  | succ i ih =>
    rw [hhSeq_succ, length_hhStep, ih]
    omega

lemma hhZeroStep_mem (G : SimpleGraph V) :
    0 ∈ hhSeq G (hhZeroStep G) ∨ hhSeq G (hhZeroStep G) = [] :=
  Nat.sInf_mem (s := {i | 0 ∈ hhSeq G i ∨ hhSeq G i = []})
    ⟨Fintype.card V, Or.inr (List.eq_nil_of_length_eq_zero (by rw [length_hhSeq]; simp))⟩

lemma mem_degSeq (G : SimpleGraph V) (a : ℕ) : a ∈ degSeq G ↔ ∃ v, G.degree v = a := by
  simp [degSeq, Multiset.mem_sort]

lemma zero_notMem_degSeq (G : SimpleGraph V) (hG : G.Connected) [Nontrivial V] :
    0 ∉ degSeq G := by
  rw [mem_degSeq]
  rintro ⟨v, hv⟩
  have := hG.preconnected.degree_pos_of_nontrivial v
  omega

/-- For a connected graph, the first zero appears at step `k ≥ 1`. -/
lemma one_le_hhZeroStep (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    1 ≤ hhZeroStep G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra h
  have h0 : hhZeroStep G = 0 := by omega
  have hm := hhZeroStep_mem G
  rw [h0] at hm
  rcases hm with hm | hm
  · exact zero_notMem_degSeq G hG hm
  · have := length_hhSeq G 0
    rw [hm] at this
    simp at this
    omega

/-- If the first zero appears at step `1`, at most `Δ` vertices have degree at least two. -/
lemma card_le_maxDegree_of_hhZeroStep (G : SimpleGraph V) (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) (h1 : hhZeroStep G = 1) :
    #(univ.filter fun v => 2 ≤ G.degree v) ≤ G.maxDegree := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hm := hhZeroStep_mem G
  rw [h1] at hm
  have hlen := length_hhSeq G 1
  obtain ⟨d, r, hdr⟩ : ∃ d r, degSeq G = d :: r := by
    cases h : degSeq G with
    | nil =>
      have := length_degSeq G
      rw [h] at this
      simp at this
      omega
    | cons d r => exact ⟨d, r, rfl⟩
  have hseq : hhSeq G 1 = hhStep (d :: r) := by
    rw [show hhSeq G 1 = hhStep (hhSeq G 0) from hhSeq_succ G 0]
    simp [hhSeq, hdr]
  rw [hseq] at hm hlen
  -- the zero comes from an entry `a ≤ 1` among the first `d` entries of `r`
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ r.take d, a ≤ 1 := by
    rcases hm with hm | hm
    · simp only [hhStep, (List.perm_insertionSort _ _).mem_iff, List.mem_append,
        List.mem_map] at hm
      rcases hm with ⟨a, ha, ha0⟩ | hm
      · exact ⟨a, ha, by omega⟩
      · exact absurd (hdr ▸ List.mem_cons_of_mem d (List.mem_of_mem_drop hm))
          (zero_notMem_degSeq G hG)
    · rw [hm] at hlen
      simp at hlen
      omega
  -- the list is nonincreasing
  have hpw : (degSeq G).Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  rw [hdr, List.pairwise_cons] at hpw
  have hr := hpw.2
  rw [← List.take_append_drop d r, List.pairwise_append] at hr
  have hdrop : ∀ b ∈ r.drop d, b ≤ 1 := fun b hb => (hr.2.2 a ha b hb).trans ha1
  -- counting entries at least two
  have hcount : #(univ.filter fun v => 2 ≤ G.degree v) =
      (degSeq G).countP (fun b => decide (2 ≤ b)) := by
    rw [← Multiset.coe_countP, degSeq, Multiset.sort_eq, Multiset.countP_map, card_def,
      filter_val]
  rw [hcount, hdr, List.countP_cons, ← List.take_append_drop d r, List.countP_append]
  have hdrop0 : (r.drop d).countP (fun b => decide (2 ≤ b)) = 0 := by
    rw [List.countP_eq_zero]
    intro b hb
    have := hdrop b hb
    simp only [decide_eq_true_eq]
    omega
  have htake : (r.take d).countP (fun b => decide (2 ≤ b)) < (r.take d).length := by
    rw [List.countP_eq_length_filter, List.length_filter_lt_length_iff_exists]
    exact ⟨a, ha, by simp only [decide_eq_true_eq]; omega⟩
  have hlt : (r.take d).length ≤ d := by
    rw [List.length_take]
    exact min_le_left _ _
  have hdΔ : d ≤ G.maxDegree := by
    obtain ⟨v, hv⟩ := (mem_degSeq G d).mp (hdr ▸ List.mem_cons_self)
    rw [← hv]
    exact G.degree_le_maxDegree v
  rw [hdrop0]
  split_ifs <;> omega

/-! ### The conjecture -/

omit [Fintype V] in
lemma indep_of_maxDegIn (G : SimpleGraph V) (D : Finset V) (h : maxDegIn G D = 0) :
    ∀ x ∈ D, ∀ y ∈ D, ¬ G.Adj x y := by
  intro x hx y hy hxy
  have hle : #(D.filter (G.Adj x)) ≤ maxDegIn G D :=
    le_sup (f := fun v => #(D.filter (G.Adj v))) hx
  rw [h, Nat.le_zero, card_eq_zero, filter_eq_empty_iff] at hle
  exact hle hy hxy

/-- **WOWII Conjecture 436c.** -/
theorem conjecture436c : Conjecture436c := by
  intro V _ G hG hn
  have h1 := twoIndepNum_le_WP_add_one G
  have hk := one_le_hhZeroStep G hG (by omega)
  have hWP : 1 ≤ WP Gᶜ :=
    le_WP Gᶜ univ 1 (by rw [card_univ]; omega) fun v _ => by omega
  have hkW : WP Gᶜ ≤ hhZeroStep G * WP Gᶜ := Nat.le_mul_of_pos_left _ hk
  by_cases hDm : 1 ≤ maxDegIn G (nbrDom G)
  · omega
  have hD := indep_of_maxDegIn G (nbrDom G) (by omega)
  by_cases hk1 : hhZeroStep G = 1
  · have := twoIndepNum_le_WP G hG (by omega) (card_le_maxDegree_of_hhZeroStep G hG (by omega) hk1)
      hD
    rw [hk1, one_mul]
    omega
  · have : 2 * WP Gᶜ ≤ hhZeroStep G * WP Gᶜ := Nat.mul_le_mul_right _ (by omega)
    omega

end WOWII436c
