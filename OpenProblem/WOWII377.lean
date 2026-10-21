import OpenProblem.WOWII372

/-!
# Written on the Wall II, Conjecture 377

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 377.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ number of isolates of <M> + upper median(T)`.

Here `γ_t` is the total domination number, `M` is the set of vertices of maximum degree, `<M>`
is the subgraph it induces, and the upper median is the entry at (0-based) position `⌊n/2⌋` of
the degree sequence sorted in nondecreasing order.

Let `I` be the set of isolates of `<M>` and `S` a total dominating set.

* In a tree fewer than half of the vertices have degree at least three, so the upper median is
  `1` or `2`, and it is `2` exactly when at most half of the vertices are leaves.
* Count edges: each `v ∈ I ∩ S` has an edge to `S`, each `v ∈ I - S` contributes all of its at
  least two edges, and each other vertex outside `S` has an edge to `S`. These edges are distinct
  and a tree has `n - 1` edges, so `|I| + 1 ≤ |S|`.
* If `|S| = |I| + 1` and the maximum degree is at least three, the count is tight: then
  `I ⊆ S`, every vertex outside `S` is a leaf, and a degree count shows that more than half of
  the vertices are leaves. If the maximum degree is two, `T` is a path and `I` is empty unless
  `T` has three vertices. So `|I| + 2 ≤ |S|` whenever at most half of the vertices are leaves.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII377

open SimpleGraph WOWII372

variable {V : Type*} [Fintype V]

/-! ### The invariants -/

/-- The vertices of maximum degree. -/
def maxDegSet (T : SimpleGraph V) : Finset V := univ.filter (fun v => T.degree v = T.maxDegree)

/-- The isolated vertices of the subgraph induced by the vertices of maximum degree. -/
def isoMax (T : SimpleGraph V) : Finset V :=
  (maxDegSet T).filter (fun v => ∀ w, T.Adj v w → w ∉ maxDegSet T)

/-- The degree sequence, sorted in nondecreasing order. -/
def degSeq (T : SimpleGraph V) : List ℕ := (univ.val.map fun v => T.degree v).sort

/-- The upper median of the degree sequence: the entry at (0-based) position `⌊n/2⌋` of the sorted
degree sequence. For odd `n` this is the median. -/
def upperMedian (T : SimpleGraph V) : ℕ := (degSeq T).getD (Fintype.card V / 2) 0

/-! ### Order statistics of a sorted list -/

omit [Fintype V] in
/-- In a sorted list, the entry at position `k` is at most `t` iff more than `k` entries are. -/
lemma getD_le_iff {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < l.length) (t : ℕ) :
    l.getD k 0 ≤ t ↔ k < l.countP (fun x => decide (x ≤ t)) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have hzero : ¬ a ≤ t → l.countP (fun x => decide (x ≤ t)) = 0 := by
      intro hat
      rw [List.countP_eq_zero]
      intro x hx
      have := hl.1 x hx
      simp only [decide_eq_true_eq]
      omega
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, List.countP_cons]
      by_cases hat : a ≤ t
      · simp [hat]
      · simp [hat, hzero hat]
    | succ k =>
      simp only [List.getD_cons_succ, List.countP_cons]
      have hk' : k < l.length := by simp at hk; omega
      rw [ih hl.2 hk']
      by_cases hat : a ≤ t
      · simp [hat]
      · simp [hat, hzero hat]

lemma length_degSeq (T : SimpleGraph V) : (degSeq T).length = Fintype.card V := by
  simp [degSeq, Multiset.length_sort]

lemma countP_degSeq (T : SimpleGraph V) (t : ℕ) :
    (degSeq T).countP (fun x => decide (x ≤ t)) = #(univ.filter (fun v => T.degree v ≤ t)) := by
  have h1 : ((degSeq T : List ℕ) : Multiset ℕ) = univ.val.map fun v => T.degree v :=
    Multiset.sort_eq _ _
  rw [← Multiset.coe_countP, h1, Multiset.countP_map, Finset.card_def, Finset.filter_val]

lemma upperMedian_le_iff (T : SimpleGraph V) (hn : 0 < Fintype.card V) (t : ℕ) :
    upperMedian T ≤ t ↔ Fintype.card V / 2 < #(univ.filter (fun v => T.degree v ≤ t)) := by
  rw [upperMedian, getD_le_iff (l := degSeq T) (Multiset.pairwise_sort _ _)
    (by rw [length_degSeq]; omega), countP_degSeq]

/-! ### Degrees in a tree -/

lemma degree_pos {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) (v : V) :
    1 ≤ T.degree v := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact hT.connected.preconnected.degree_pos_of_nontrivial v

lemma sum_degree {T : SimpleGraph V} (hT : T.IsTree) :
    ∑ v, T.degree v + 2 = 2 * Fintype.card V := by
  have h1 := T.sum_degrees_eq_twice_card_edges
  have h2 := hT.card_edgeFinset
  omega

/-- In a tree, fewer than half of the vertices have degree at least three, and at least two
vertices are leaves. -/
lemma card_deg_ge {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    2 * #(univ.filter (fun v => ¬ T.degree v ≤ 2)) + 2 ≤ Fintype.card V ∧
    #(univ.filter (fun v => ¬ T.degree v ≤ 1)) + 2 ≤ Fintype.card V := by
  have hs := sum_degree hT
  have hp := degree_pos hT hn
  constructor
  · have hle : ∑ v, (1 + 2 * (if ¬ T.degree v ≤ 2 then 1 else 0)) ≤ ∑ v, T.degree v :=
      Finset.sum_le_sum fun v _ => by have := hp v; split_ifs <;> omega
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at hle
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Nat.cast_id] at hle
    omega
  · have hle : ∑ v, (1 + (if ¬ T.degree v ≤ 1 then 1 else 0)) ≤ ∑ v, T.degree v :=
      Finset.sum_le_sum fun v _ => by have := hp v; split_ifs <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_boole] at hle
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Nat.cast_id] at hle
    omega

lemma card_filter_le_add (T : SimpleGraph V) (t : ℕ) :
    #(univ.filter (fun v => T.degree v ≤ t)) + #(univ.filter (fun v => ¬ T.degree v ≤ t)) =
      Fintype.card V := by
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- In a tree the upper median of the degree sequence is at most two. -/
lemma upperMedian_le_two {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    upperMedian T ≤ 2 := by
  rw [upperMedian_le_iff T (by omega)]
  have := (card_deg_ge hT hn).1
  have := card_filter_le_add T 2
  omega

/-- If the upper median is at least two, at most half of the vertices are leaves. -/
lemma two_mul_leaves_le {T : SimpleGraph V} (hn : 1 ≤ Fintype.card V) (h : 2 ≤ upperMedian T) :
    2 * #(univ.filter (fun v => T.degree v ≤ 1)) ≤ Fintype.card V := by
  have h1 : ¬ upperMedian T ≤ 1 := by omega
  rw [upperMedian_le_iff T (by omega)] at h1
  omega

omit [Fintype V] in
lemma eq_of_degree_le_one {T : SimpleGraph V} [Fintype V] {a b c : V} (h : T.degree a ≤ 1)
    (hb : T.Adj a b) (hc : T.Adj a c) : b = c := by
  by_contra hne
  have : #({b, c} : Finset V) ≤ #(T.neighborFinset a) :=
    card_le_card fun x hx => by
      rcases mem_insert.mp hx with rfl | hx
      · exact (T.mem_neighborFinset a x).mpr hb
      · rw [mem_singleton.mp hx]; exact (T.mem_neighborFinset a c).mpr hc
  rw [card_pair hne, card_neighborFinset_eq_degree] at this
  omega

/-! ### Isolates of `<M>` -/

lemma maxDegSet_of_mem_isoMax {T : SimpleGraph V} {v : V} (hv : v ∈ isoMax T) :
    v ∈ maxDegSet T :=
  (mem_filter.mp hv).1

lemma degree_of_mem_isoMax {T : SimpleGraph V} {v : V} (hv : v ∈ isoMax T) :
    T.degree v = T.maxDegree := by
  have := maxDegSet_of_mem_isoMax hv
  simpa [maxDegSet] using this

lemma not_mem_isoMax_of_adj {T : SimpleGraph V} {v w : V} (hv : v ∈ isoMax T)
    (h : T.Adj v w) : w ∉ isoMax T :=
  fun hw => (mem_filter.mp hv).2 w h (maxDegSet_of_mem_isoMax hw)

lemma degree_lt_of_adj_isoMax {T : SimpleGraph V} {v w : V} (hv : v ∈ isoMax T)
    (h : T.Adj v w) : T.degree w < T.degree v := by
  have h1 : w ∉ maxDegSet T := (mem_filter.mp hv).2 w h
  simp only [maxDegSet, mem_filter, mem_univ, true_and] at h1
  have h2 := T.degree_le_maxDegree w
  rw [degree_of_mem_isoMax hv]
  omega

lemma two_le_degree_of_mem_isoMax {T : SimpleGraph V} (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card V) {v : V} (hv : v ∈ isoMax T) : 2 ≤ T.degree v := by
  obtain ⟨w, hw⟩ := (T.degree_pos_iff_exists_adj v).mp (degree_pos hT hn v)
  have := degree_lt_of_adj_isoMax hv hw
  have := degree_pos hT hn w
  omega

/-! ### Counting edges -/

/-- Edges from the isolates of `<M>` in `S` to `S`. -/
def F1 (T : SimpleGraph V) (S : Finset V) (σ : V → V) : Finset (Sym2 V) :=
  ((isoMax T).filter (· ∈ S)).image (fun v => s(v, σ v))

/-- All edges at the isolates of `<M>` outside `S`. -/
def F2 (T : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  ((isoMax T).filter (· ∉ S)).biUnion (fun v => T.incidenceFinset v)

/-- Edges from the other vertices outside `S` to `S`. -/
def F3 (T : SimpleGraph V) (S : Finset V) (σ : V → V) : Finset (Sym2 V) :=
  (univ.filter (fun v => v ∉ S ∧ v ∉ isoMax T)).image (fun y => s(y, σ y))

section count

variable {T : SimpleGraph V} {S : Finset V} {σ : V → V} (hσS : ∀ v, σ v ∈ S)
  (hσ : ∀ v, T.Adj v (σ v))

include hσ in
lemma card_F1 : #(F1 T S σ) = #((isoMax T).filter (· ∈ S)) := by
  apply card_image_of_injOn
  intro v hv w hw h
  have hv' := (mem_filter.mp hv).1
  have hw' := (mem_filter.mp hw).1
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd (h1 ▸ hv') (not_mem_isoMax_of_adj hw' (hσ w))

include hσS in
lemma card_F3 : #(F3 T S σ) = #(univ.filter (fun v => v ∉ S ∧ v ∉ isoMax T)) := by
  apply card_image_of_injOn
  intro v hv w hw h
  have hv' := (mem_filter.mp hv).2
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd (h1 ▸ hσS w) hv'.1

lemma card_F2 : #(F2 T S) = ∑ v ∈ (isoMax T).filter (· ∉ S), T.degree v := by
  rw [F2, card_biUnion]
  · simp [card_incidenceFinset_eq_degree]
  · intro v hv w hw hvw
    show Disjoint (T.incidenceFinset v) (T.incidenceFinset w)
    rw [Finset.disjoint_left]
    intro e hev hew
    rw [mem_incidenceFinset] at hev hew
    have he : e = s(v, w) := (Sym2.mem_and_mem_iff hvw).mp ⟨hev.2, hew.2⟩
    have hadj : T.Adj v w := by
      rw [← SimpleGraph.mem_edgeSet, ← he]
      exact hev.1
    exact not_mem_isoMax_of_adj (mem_filter.mp hv).1 hadj (mem_filter.mp hw).1

include hσ in
lemma F_subset : F1 T S σ ∪ F2 T S ∪ F3 T S σ ⊆ T.edgeFinset := by
  intro e he
  rcases mem_union.mp he with he | he
  · rcases mem_union.mp he with he | he
    · obtain ⟨v, -, rfl⟩ := mem_image.mp he
      exact T.mem_edgeFinset.mpr (hσ v)
    · obtain ⟨v, -, hv⟩ := mem_biUnion.mp he
      rw [mem_incidenceFinset] at hv
      exact T.mem_edgeFinset.mpr hv.1
  · obtain ⟨v, -, rfl⟩ := mem_image.mp he
    exact T.mem_edgeFinset.mpr (hσ v)

include hσS in
lemma disjoint_F12 : Disjoint (F1 T S σ) (F2 T S) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  obtain ⟨v, hv, rfl⟩ := mem_image.mp he1
  obtain ⟨w, hw, hwe⟩ := mem_biUnion.mp he2
  rw [mem_incidenceFinset] at hwe
  have hvS := (mem_filter.mp hv).2
  have hwS := (mem_filter.mp hw).2
  rcases Sym2.mem_iff.mp hwe.2 with rfl | rfl
  · exact hwS hvS
  · exact hwS (hσS v)

include hσS in
lemma disjoint_F13 : Disjoint (F1 T S σ) (F3 T S σ) := by
  rw [Finset.disjoint_left]
  intro e he1 he3
  obtain ⟨v, hv, rfl⟩ := mem_image.mp he1
  obtain ⟨y, hy, h⟩ := mem_image.mp he3
  have hvS := (mem_filter.mp hv).2
  have hyS := (mem_filter.mp hy).2.1
  rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hyS hvS
  · exact hyS (hσS v)

include hσS in
lemma disjoint_F23 : Disjoint (F2 T S) (F3 T S σ) := by
  rw [Finset.disjoint_left]
  intro e he2 he3
  obtain ⟨w, hw, hwe⟩ := mem_biUnion.mp he2
  rw [mem_incidenceFinset] at hwe
  obtain ⟨y, hy, rfl⟩ := mem_image.mp he3
  have hwI := (mem_filter.mp hw).1
  have hwS := (mem_filter.mp hw).2
  have hyI := (mem_filter.mp hy).2.2
  rcases Sym2.mem_iff.mp hwe.2 with rfl | rfl
  · exact hyI hwI
  · exact hwS (hσS y)

include hσS in
lemma card_union_F : #(F1 T S σ ∪ F2 T S ∪ F3 T S σ) = #(F1 T S σ) + #(F2 T S) + #(F3 T S σ) := by
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_F13 hσS, disjoint_F23 hσS⟩),
    card_union_of_disjoint (disjoint_F12 hσS)]

include hσS hσ in
lemma count (hT : T.IsTree) :
    #((isoMax T).filter (· ∈ S)) + ∑ v ∈ (isoMax T).filter (· ∉ S), T.degree v +
      #(univ.filter (fun v => v ∉ S ∧ v ∉ isoMax T)) + 1 ≤ Fintype.card V := by
  have h1 := card_le_card (F_subset (S := S) hσ)
  rw [card_union_F hσS, card_F1 hσ, card_F2, card_F3 hσS] at h1
  have h2 := hT.card_edgeFinset
  omega

end count

lemma card_partition (T : SimpleGraph V) (S : Finset V) :
    #S + #((isoMax T).filter (· ∉ S)) + #(univ.filter (fun v => v ∉ S ∧ v ∉ isoMax T)) =
      Fintype.card V := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset V)) (p := (· ∈ S))
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter (· ∉ S))
    (p := (· ∈ isoMax T))
  have e1 : univ.filter (· ∈ S) = S := by ext; simp
  have e2 : (univ.filter (· ∉ S)).filter (· ∈ isoMax T) = (isoMax T).filter (· ∉ S) := by
    ext; simp [and_comm]
  have e3 : (univ.filter (· ∉ S)).filter (· ∉ isoMax T) =
      univ.filter (fun v => v ∉ S ∧ v ∉ isoMax T) := by
    ext; simp
  rw [e1, card_univ] at h1
  rw [e2, e3] at h2
  omega

/-! ### The two bounds -/

/-- For every total dominating set `S` of a tree, `|I| + 1 ≤ |S|`. -/
lemma iso_add_one_le {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V)
    {S : Finset V} (hS : IsTDS T S) : #(isoMax T) + 1 ≤ #S := by
  choose σ hσS hσ using hS
  have hc := count hσS hσ hT
  have h2 : #((isoMax T).filter (· ∉ S)) • 2 ≤ ∑ v ∈ (isoMax T).filter (· ∉ S), T.degree v :=
    Finset.card_nsmul_le_sum _ _ _ fun v hv =>
      two_le_degree_of_mem_isoMax hT hn (mem_filter.mp hv).1
  rw [smul_eq_mul] at h2
  have hI := Finset.card_filter_add_card_filter_not (s := isoMax T) (p := (· ∈ S))
  have hV := card_partition T S
  omega

/-- For every total dominating set `S` of a tree in which at most half of the vertices are
leaves, `|I| + 2 ≤ |S|`. -/
lemma iso_add_two_le {T : SimpleGraph V} (hT : T.IsTree) (hn : 3 ≤ Fintype.card V)
    {S : Finset V} (hS : IsTDS T S)
    (hleaf : 2 * #(univ.filter (fun v => T.degree v ≤ 1)) ≤ Fintype.card V) :
    #(isoMax T) + 2 ≤ #S := by
  by_contra hlt
  have hA := iso_add_one_le hT (by omega) hS
  have hSI : #S = #(isoMax T) + 1 := by omega
  rcases (isoMax T).eq_empty_or_nonempty with hI0 | ⟨v0, hv0⟩
  · -- no isolates: a total dominating set has at least two vertices
    rw [hI0, card_empty, zero_add] at hSI
    obtain ⟨a, rfl⟩ := card_eq_one.mp hSI
    obtain ⟨u, hu, hau⟩ := hS a
    rw [mem_singleton.mp hu] at hau
    exact T.irrefl hau
  have hdeg0 := two_le_degree_of_mem_isoMax hT (by omega) hv0
  by_cases hΔ : 3 ≤ T.maxDegree
  · -- the count is tight: every vertex outside `S` is a leaf
    choose σ hσS hσ using hS
    have hc := count hσS hσ hT
    have h3 : #((isoMax T).filter (· ∉ S)) • 3 ≤ ∑ v ∈ (isoMax T).filter (· ∉ S), T.degree v :=
      Finset.card_nsmul_le_sum _ _ _ fun v hv => by
        rw [degree_of_mem_isoMax (mem_filter.mp hv).1]; exact hΔ
    rw [smul_eq_mul] at h3
    have hI := Finset.card_filter_add_card_filter_not (s := isoMax T) (p := (· ∈ S))
    have hV := card_partition T S
    have hIY : (isoMax T).filter (· ∉ S) = ∅ := card_eq_zero.mp (by omega)
    have hIS : ∀ v ∈ isoMax T, v ∈ S := by
      intro v hv
      by_contra h
      have : v ∈ (isoMax T).filter (· ∉ S) := mem_filter.mpr ⟨hv, h⟩
      rw [hIY] at this
      exact absurd this (Finset.notMem_empty v)
    have hE := hT.card_edgeFinset
    have hsub : F1 T S σ ∪ F3 T S σ ⊆ T.edgeFinset := fun e he =>
      F_subset (S := S) hσ (mem_union.mpr (by
        rcases mem_union.mp he with h | h
        · exact Or.inl (mem_union_left _ h)
        · exact Or.inr h))
    have hcard13 : #(F1 T S σ ∪ F3 T S σ) = #(F1 T S σ) + #(F3 T S σ) :=
      card_union_of_disjoint (disjoint_F13 hσS)
    rw [card_F1 hσ, card_F3 hσS] at hcard13
    rw [hIY, card_empty] at hV
    have hEq : F1 T S σ ∪ F3 T S σ = T.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hleafY : ∀ y, y ∉ S → T.degree y ≤ 1 := by
      intro y hy
      rw [← card_neighborFinset_eq_degree]
      calc #(T.neighborFinset y) ≤ #({σ y} : Finset V) := by
            apply card_le_card
            intro w hw
            have hyw : T.Adj y w := (T.mem_neighborFinset y w).mp hw
            have he : s(y, w) ∈ F1 T S σ ∪ F3 T S σ := by
              rw [hEq]; exact T.mem_edgeFinset.mpr hyw
            rcases mem_union.mp he with he | he
            · obtain ⟨u, hu, h⟩ := mem_image.mp he
              have huS := (mem_filter.mp hu).2
              rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨-, rfl⟩
              · exact absurd huS hy
              · exact absurd (hσS u) hy
            · obtain ⟨u, hu, h⟩ := mem_image.mp he
              rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
              · exact mem_singleton_self _
              · exact absurd (hσS u) hy
        _ = 1 := card_singleton _
    -- a degree count
    have hs := sum_degree hT
    have hp := degree_pos hT (by omega)
    have h1 : ∑ v, (1 + (if v ∈ S then 1 else 0) + (if v ∈ isoMax T then 1 else 0)) ≤
        ∑ v, (T.degree v + (if v ∈ S ∧ v ∉ isoMax T ∧ T.degree v ≤ 1 then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro v _
      have := hp v
      by_cases hvI : v ∈ isoMax T
      · have := degree_of_mem_isoMax hvI
        simp only [hIS v hvI, hvI, not_true_eq_false, false_and, and_false, ite_true, ite_false]
        omega
      · by_cases hvS : v ∈ S
        · simp only [hvS, hvI, not_false_eq_true, true_and, ite_true, ite_false]
          split_ifs <;> omega
        · simp only [hvS, hvI, false_and, ite_false]
          omega
    have h2 : ∑ v, ((if v ∉ S then 1 else 0) +
        (if v ∈ S ∧ v ∉ isoMax T ∧ T.degree v ≤ 1 then 1 else 0)) ≤
        ∑ v, (if T.degree v ≤ 1 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hvS : v ∈ S
      · simp only [hvS, not_true_eq_false, true_and, ite_false, zero_add]
        split_ifs <;> omega
      · have := hleafY v hvS
        simp only [hvS, not_false_eq_true, false_and, ite_true, ite_false, this]
        omega
    simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one, Nat.cast_id] at h1 h2
    have e1 : univ.filter (· ∈ S) = S := by ext; simp
    have e2 : univ.filter (· ∈ isoMax T) = isoMax T := by ext; simp
    have e3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset V)) (p := (· ∈ S))
    rw [e1, card_univ] at e3
    simp only [e1, e2] at h1
    omega
  · -- maximum degree two: `v0` and its two leaf neighbours form a component
    have hd0 : T.degree v0 = 2 := by
      have := degree_of_mem_isoMax hv0
      omega
    obtain ⟨u, w, huw, hN⟩ := card_eq_two.mp
      (by rw [card_neighborFinset_eq_degree]; exact hd0 : #(T.neighborFinset v0) = 2)
    have hu : T.Adj v0 u := (T.mem_neighborFinset v0 u).mp (by rw [hN]; simp)
    have hw : T.Adj v0 w := (T.mem_neighborFinset v0 w).mp (by rw [hN]; simp)
    have hdu : T.degree u ≤ 1 := by have := degree_lt_of_adj_isoMax hv0 hu; omega
    have hdw : T.degree w ≤ 1 := by have := degree_lt_of_adj_isoMax hv0 hw; omega
    have hl2 : 2 ≤ #(univ.filter (fun v => T.degree v ≤ 1)) := by
      calc 2 = #({u, w} : Finset V) := (card_pair huw).symm
        _ ≤ _ := card_le_card fun x hx => by
          rcases mem_insert.mp hx with rfl | hx
          · simpa using hdu
          · rw [mem_singleton.mp hx]; simpa using hdw
    let C : Finset V := {v0, u, w}
    have hC : #C ≤ 3 := card_le_three
    obtain ⟨z, hz⟩ : ∃ z, z ∉ C := by
      by_contra h
      push Not at h
      have : #(univ : Finset V) ≤ #C := card_le_card fun x _ => h x
      rw [card_univ] at this
      omega
    have hclosed : ∀ a b, T.Adj a b → a ∈ (C : Set V) → b ∈ (C : Set V) := by
      intro a b hab ha
      simp only [C, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · have : b ∈ T.neighborFinset a := (T.mem_neighborFinset a b).mpr hab
        rw [hN] at this
        simp only [mem_insert, mem_singleton] at this
        tauto
      · exact Or.inl (eq_of_degree_le_one hdu hab hu.symm)
      · exact Or.inl (eq_of_degree_le_one hdw hab hw.symm)
    exact not_reachable_of_closed (C : Set V) (by simp [C]) (by simpa using hz) hclosed
      (hT.connected.preconnected v0 z)

/-! ### The conjecture -/

/-- **WOWII Conjecture 377.** For every tree `T` on more than two vertices,
`γ_t(T) ≥ (number of isolates of <M>) + (upper median of the degree sequence)`. -/
theorem conjecture377 (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 < Fintype.card V) :
    #(isoMax T) + upperMedian T ≤ totalDomNum T := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnoiso : ∀ v, ∃ u, T.Adj v u := fun v =>
    (T.degree_pos_iff_exists_adj v).mp (hT.connected.preconnected.degree_pos_of_nontrivial v)
  obtain ⟨S, hS, hScard⟩ := exists_tds_card_eq hnoiso
  rw [← hScard]
  have hmed := upperMedian_le_two hT (by omega)
  rcases Nat.lt_or_ge (upperMedian T) 2 with h | h
  · have := iso_add_one_le hT (by omega) hS
    omega
  · have := iso_add_two_le hT hn hS (two_mul_leaves_le (by omega) h)
    omega

end WOWII377
