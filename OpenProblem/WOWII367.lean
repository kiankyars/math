import OpenProblem.WOWII378

/-!
# Written on the Wall II, Conjecture 367

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 367.** If `T` is a tree on `n > 2` vertices such that the most frequently
> occurring degree is two, then `γ_t(T) ≥ (4/3) dd(T)`.

Here `γ_t` is the total domination number and `dd(T)` is the number of distinct vertex degrees.

* If "the most frequently occurring degree is two" means that degree two occurs strictly more
  often than every other degree, the conjecture is true (`conjecture367`). We only use that
  there are more vertices of degree two than leaves.
* If ties are allowed, the conjecture is false (`not_conjecture367_ties`): a 12-vertex tree with
  five leaves, five vertices of degree two and four distinct degrees has `γ_t = 5 < 16/3`.

The proof combines two counts for a total dominating set `S` of a tree.

* **Edges.** Count three families of edges:
  - one edge from each vertex of `S` to `S`, giving at least `⌈|S|/2⌉` edges;
  - one edge from each vertex outside `S` to `S`;
  - one further edge at each non-leaf outside `S`, counted at most twice.

  This gives `#non-leaves + 2 ≤ |S| + 2⌊|S|/2⌋`.
* **Leaves.** The degree sum gives `#leaves = 2 + ∑_{deg v ≥ 3} (deg v - 2)`. If `m` distinct
  degrees are at least three, this is at least `2 + m(m+1)/2`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII367

open SimpleGraph WOWII372 WOWII377

variable {V : Type*} [Fintype V]

/-- The number of distinct vertex degrees. -/
def dd (T : SimpleGraph V) : ℕ := #(univ.image fun v => T.degree v)

/-! ### A refined edge count -/

/-- For a total dominating set `S` of a tree, `#non-leaves + 2 ≤ |S| + 2⌊|S|/2⌋`. -/
lemma nonleaves_le {T : SimpleGraph V} (hT : T.IsTree) {S : Finset V} (hS : IsTDS T S) :
    #(univ.filter fun v => ¬ T.degree v ≤ 1) + 2 ≤ #S + 2 * (#S / 2) := by
  choose σ hσS hσ using hS
  set Y' := univ.filter (fun v => v ∉ S ∧ ¬ T.degree v ≤ 1) with hY'
  have hτ : ∀ y ∈ Y', ∃ w, T.Adj y w ∧ w ≠ σ y := by
    intro y hy
    have hdeg : 1 < #(T.neighborFinset y) := by
      rw [card_neighborFinset_eq_degree]; have := (mem_filter.mp hy).2.2; omega
    obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne hdeg (σ y)
    exact ⟨w, (T.mem_neighborFinset y w).mp hw, hne⟩
  choose! τ hτadj hτne using hτ
  let E1 := S.image (fun s => s(s, σ s))
  let E2 := Sᶜ.image (fun y => s(y, σ y))
  let E3 := Y'.image (fun y => s(y, τ y))
  -- `E1` is hit at most twice by `S`
  have h1 : #S ≤ 2 * #E1 := by
    apply Finset.card_le_mul_card_image
    intro e _
    induction e using Sym2.ind with
    | h x y =>
      calc #{v ∈ S | s(v, σ v) = s(x, y)} ≤ #({x, y} : Finset V) := by
            apply Finset.card_le_card
            intro v hv
            rw [Finset.mem_filter] at hv
            have := hv.2 ▸ Sym2.mem_mk_left v (σ v)
            rcases Sym2.mem_iff.mp this with rfl | rfl <;> simp
        _ ≤ 2 := Finset.card_le_two
  -- `E2` is hit once by each vertex outside `S`
  have h2 : #E2 = #Sᶜ := by
    apply card_image_of_injOn
    intro v hv w hw h
    have hv' : v ∉ S := Finset.mem_compl.mp hv
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd (h1 ▸ hσS w) hv'
  -- `E3` is hit at most twice by `Y'`
  have h3 : #Y' ≤ 2 * #E3 := by
    apply Finset.card_le_mul_card_image
    intro e _
    induction e using Sym2.ind with
    | h x y =>
      calc #{v ∈ Y' | s(v, τ v) = s(x, y)} ≤ #({x, y} : Finset V) := by
            apply Finset.card_le_card
            intro v hv
            rw [Finset.mem_filter] at hv
            have := hv.2 ▸ Sym2.mem_mk_left v (τ v)
            rcases Sym2.mem_iff.mp this with rfl | rfl <;> simp
        _ ≤ 2 := Finset.card_le_two
  -- the three families are disjoint sets of edges
  have hd12 : Disjoint E1 E2 := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he1
    obtain ⟨y, hy, h⟩ := mem_image.mp he2
    have hyS : y ∉ S := Finset.mem_compl.mp hy
    rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hyS hs
    · exact hyS (hσS s)
  have hd13 : Disjoint E1 E3 := by
    rw [Finset.disjoint_left]
    intro e he1 he3
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he1
    obtain ⟨y, hy, h⟩ := mem_image.mp he3
    have hyS : y ∉ S := (mem_filter.mp hy).2.1
    rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hyS hs
    · exact hyS (hσS s)
  have hd23 : Disjoint E2 E3 := by
    rw [Finset.disjoint_left]
    intro e he2 he3
    obtain ⟨y, hy, rfl⟩ := mem_image.mp he2
    obtain ⟨y', hy', h⟩ := mem_image.mp he3
    have hy'S : y' ∉ S := (mem_filter.mp hy').2.1
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · subst h1
      exact hτne y' hy' h2
    · exact hy'S (by rw [h1]; exact hσS y)
  have hsub : E1 ∪ E2 ∪ E3 ⊆ T.edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · obtain ⟨v, -, rfl⟩ := mem_image.mp he
        exact T.mem_edgeFinset.mpr (hσ v)
      · obtain ⟨v, -, rfl⟩ := mem_image.mp he
        exact T.mem_edgeFinset.mpr (hσ v)
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp he
      exact T.mem_edgeFinset.mpr (hτadj v hv)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd13, hd23⟩),
    card_union_of_disjoint hd12] at hcard
  have hE := hT.card_edgeFinset
  have hSc : #Sᶜ + #S = Fintype.card V := by rw [Finset.card_compl]; have := card_le_univ S; omega
  -- every non-leaf lies in `S` or in `Y'`
  have hnl : #(univ.filter fun v => ¬ T.degree v ≤ 1) ≤ #S + #Y' := by
    calc #(univ.filter fun v => ¬ T.degree v ≤ 1) ≤ #(S ∪ Y') := by
          apply card_le_card
          intro v hv
          by_cases hvS : v ∈ S
          · exact mem_union_left _ hvS
          · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ v, hvS, (mem_filter.mp hv).2⟩)
      _ ≤ #S + #Y' := card_union_le _ _
  omega

/-! ### Counting leaves through distinct degrees -/

/-- `m` distinct integers that are at least `3` satisfy `m(m+1) ≤ 2 ∑ (x - 2)`. -/
lemma card_mul_le_sum (s : Finset ℕ) (hs : ∀ x ∈ s, 3 ≤ x) :
    #s * (#s + 1) ≤ 2 * ∑ x ∈ s, (x - 2) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have h3 : 3 ≤ a := hs a (mem_insert_self a s)
    have ih' := ih fun x hx => hs x (mem_insert_of_mem hx)
    have hcs : #s ≤ a - 3 := by
      calc #s ≤ #(Finset.Ico 3 a) := card_le_card fun x hx =>
            Finset.mem_Ico.mpr ⟨hs x (mem_insert_of_mem hx), hlt x hx⟩
        _ = a - 3 := Nat.card_Ico 3 a
    rw [card_insert_of_notMem ha, sum_insert ha]
    have : (#s + 1) * (#s + 1 + 1) = #s * (#s + 1) + 2 * (#s + 1) := by ring
    omega

/-- In a tree on at least two vertices, `#leaves ≥ 2 + m(m+1)/2`, where `m` is the number of
distinct degrees that are at least three. Returned as `2 ∑ ≥ m(m+1)`, `#leaves ≥ 2 + ∑`. -/
lemma leaves_ge {T : SimpleGraph V} (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    ∃ σ : ℕ, #((univ.filter fun v => 3 ≤ T.degree v).image fun v => T.degree v) *
        (#((univ.filter fun v => 3 ≤ T.degree v).image fun v => T.degree v) + 1) ≤ 2 * σ ∧
      2 + σ ≤ #(univ.filter fun v => T.degree v ≤ 1) := by
  set H := univ.filter fun v => 3 ≤ T.degree v
  set D3 := H.image fun v => T.degree v
  refine ⟨∑ d ∈ D3, (d - 2), card_mul_le_sum D3 fun d hd => ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hd
    exact (mem_filter.mp hv).2
  · have hp := WOWII377.degree_pos hT hn
    have hs := WOWII377.sum_degree hT
    -- split the degree sum into leaves, degree-two vertices and the rest
    have hsplit : ∑ v, T.degree v = #(univ.filter fun v => T.degree v ≤ 1) +
        2 * #(univ.filter fun v => T.degree v = 2) + ∑ v ∈ H, (T.degree v - 2) + 2 * #H := by
      have e1 := Finset.sum_filter_add_sum_filter_not (univ : Finset V)
        (fun v => T.degree v ≤ 1) (fun v => T.degree v)
      have e2 := Finset.sum_filter_add_sum_filter_not (univ.filter fun v => ¬ T.degree v ≤ 1)
        (fun v => T.degree v = 2) (fun v => T.degree v)
      have hL : ∑ v ∈ univ.filter (fun v => T.degree v ≤ 1), T.degree v =
          #(univ.filter fun v => T.degree v ≤ 1) := by
        rw [card_eq_sum_ones]
        exact Finset.sum_congr rfl fun v hv => by
          have := (mem_filter.mp hv).2; have := hp v; omega
      have f2 : (univ.filter fun v => ¬ T.degree v ≤ 1).filter (fun v => T.degree v = 2) =
          univ.filter fun v => T.degree v = 2 := by
        ext v; simp only [mem_filter, mem_univ, true_and]; omega
      have f3 : (univ.filter fun v => ¬ T.degree v ≤ 1).filter (fun v => ¬ T.degree v = 2) = H := by
        ext v; simp only [H, mem_filter, mem_univ, true_and]; omega
      have hD2 : ∑ v ∈ univ.filter (fun v => T.degree v = 2), T.degree v =
          2 * #(univ.filter fun v => T.degree v = 2) := by
        rw [Finset.sum_congr rfl fun v hv => (mem_filter.mp hv).2, sum_const, smul_eq_mul,
          mul_comm]
      have hH : ∑ v ∈ H, T.degree v = ∑ v ∈ H, (T.degree v - 2) + 2 * #H := by
        rw [card_eq_sum_ones, mul_sum, ← sum_add_distrib]
        exact Finset.sum_congr rfl fun v hv => by
          have := (mem_filter.mp hv).2; omega
      rw [f2, f3, hD2, hH] at e2
      rw [← e1, ← e2, hL]
      ring
    -- every vertex is a leaf, has degree two or lies in `H`
    have hpart : #(univ.filter fun v => T.degree v ≤ 1) +
        #(univ.filter fun v => T.degree v = 2) + #H = Fintype.card V := by
      have e1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
        (p := fun v => T.degree v ≤ 1)
      have e2 := Finset.card_filter_add_card_filter_not
        (s := univ.filter fun v => ¬ T.degree v ≤ 1) (p := fun v => T.degree v = 2)
      have f2 : (univ.filter fun v => ¬ T.degree v ≤ 1).filter (fun v => T.degree v = 2) =
          univ.filter fun v => T.degree v = 2 := by
        ext v; simp only [mem_filter, mem_univ, true_and]; omega
      have f3 : (univ.filter fun v => ¬ T.degree v ≤ 1).filter (fun v => ¬ T.degree v = 2) = H := by
        ext v; simp only [H, mem_filter, mem_univ, true_and]; omega
      rw [f2, f3] at e2
      rw [card_univ] at e1
      omega
    -- each distinct degree in `H` is attained at least once
    have hfib : ∑ d ∈ D3, (d - 2) ≤ ∑ v ∈ H, (T.degree v - 2) := by
      rw [Finset.sum_comp (fun d => d - 2) (fun v => T.degree v)]
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hd
      have : 1 ≤ #{a ∈ H | T.degree a = T.degree v} :=
        Finset.card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, rfl⟩⟩
      rw [smul_eq_mul]
      exact Nat.le_mul_of_pos_left _ this
    omega

/-! ### The conjecture -/

/-- **WOWII Conjecture 367** (degree two strictly more frequent than degree one suffices):
for a tree `T` on more than two vertices with more vertices of degree two than leaves,
`4 dd(T) ≤ 3 γ_t(T)`. -/
theorem conjecture367 (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 < Fintype.card V)
    (hmode : #(univ.filter fun v => T.degree v = 1) < #(univ.filter fun v => T.degree v = 2)) :
    4 * dd T ≤ 3 * totalDomNum T := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnoiso : ∀ v, ∃ u, T.Adj v u := fun v =>
    (T.degree_pos_iff_exists_adj v).mp (hT.connected.preconnected.degree_pos_of_nontrivial v)
  obtain ⟨S, hS, hScard⟩ := exists_tds_card_eq hnoiso
  rw [← hScard]
  have hp := WOWII377.degree_pos hT (by omega)
  set H := univ.filter fun v => 3 ≤ T.degree v
  set D3 := H.image fun v => T.degree v
  obtain ⟨σ, hσ1, hσ2⟩ := leaves_ge hT (by omega)
  have hcount := nonleaves_le hT hS
  -- leaves are exactly the vertices of degree at most one
  have hleaf : univ.filter (fun v => T.degree v = 1) = univ.filter fun v => T.degree v ≤ 1 := by
    ext v; simp only [mem_filter, mem_univ, true_and]; have := hp v; omega
  rw [hleaf] at hmode
  -- non-leaves are the vertices of degree two together with `H`
  have hnl : #(univ.filter fun v => ¬ T.degree v ≤ 1) =
      #(univ.filter fun v => T.degree v = 2) + #H := by
    have e := Finset.card_filter_add_card_filter_not
      (s := univ.filter fun v => ¬ T.degree v ≤ 1) (p := fun v => T.degree v = 2)
    have f2 : (univ.filter fun v => ¬ T.degree v ≤ 1).filter (fun v => T.degree v = 2) =
        univ.filter fun v => T.degree v = 2 := by
      ext v; simp only [mem_filter, mem_univ, true_and]; omega
    have f3 : (univ.filter fun v => ¬ T.degree v ≤ 1).filter (fun v => ¬ T.degree v = 2) = H := by
      ext v; simp only [H, mem_filter, mem_univ, true_and]; omega
    rw [f2, f3] at e
    omega
  have hHm : #D3 ≤ #H := card_image_le
  -- the distinct degrees are `1`, `2` and those in `D3`
  have hdd : dd T ≤ #D3 + 2 := by
    have : univ.image (fun v => T.degree v) ⊆ insert 1 (insert 2 D3) := by
      intro d hd
      obtain ⟨v, -, rfl⟩ := mem_image.mp hd
      have := hp v
      by_cases h1 : T.degree v = 1
      · rw [h1]; exact mem_insert_self _ _
      by_cases h2 : T.degree v = 2
      · rw [h2]; exact mem_insert_of_mem (mem_insert_self _ _)
      exact mem_insert_of_mem (mem_insert_of_mem
        (mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ v, by omega⟩, rfl⟩))
    calc dd T ≤ #(insert 1 (insert 2 D3)) := card_le_card this
      _ ≤ #(insert 2 D3) + 1 := card_insert_le _ _
      _ ≤ #D3 + 1 + 1 := by have := card_insert_le 2 D3; omega
  -- linear consequences of `m(m+1) ≤ 2σ`
  set m := #D3
  have hm1 : m ≤ σ := by
    rcases Nat.eq_zero_or_pos m with h | h
    · omega
    · nlinarith
  have hm3 : 3 * m ≤ σ + 3 := by
    rcases Nat.lt_or_ge m 6 with h | h
    · interval_cases m <;> omega
    · nlinarith
  omega

/-- **WOWII Conjecture 367** with the strict reading of "most frequent", in the stated form
`γ_t(T) ≥ (4/3) dd(T)`. -/
theorem conjecture367_real (T : SimpleGraph V) (hT : T.IsTree) (hn : 2 < Fintype.card V)
    (hmode : ∀ d, d ≠ 2 →
      #(univ.filter fun v => T.degree v = d) < #(univ.filter fun v => T.degree v = 2)) :
    (4 / 3 : ℝ) * dd T ≤ totalDomNum T := by
  have h := conjecture367 T hT hn (hmode 1 (by decide))
  have h' : ((4 * dd T : ℕ) : ℝ) ≤ ((3 * totalDomNum T : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-! ### Ties make the conjecture false -/

/-- The edges of `T12`. -/
def E12 : List (Fin 12 × Fin 12) :=
  [(0, 8), (0, 10), (1, 8), (1, 11), (2, 9), (2, 11), (3, 9), (4, 10), (5, 10), (6, 11), (7, 11)]

def adj12 (a b : Fin 12) : Bool := E12.contains (a, b) || E12.contains (b, a)

/-- A tree with five leaves, five vertices of degree two, one of degree three and one of
degree four. -/
def T12 : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adj12 a b = true

lemma T12_adj {a b : Fin 12} : T12.Adj a b ↔ adj12 a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adj12 a b = true ∨ adj12 b a = true)) ↔ adj12 a b = true := by
    decide
  simpa [T12] using h a b

lemma T12_degree (v : Fin 12) : T12.degree v = #(univ.filter (fun w => adj12 v w = true)) :=
  WOWII378.degree_eq_card_filter T12 adj12 (fun _ _ => T12_adj) v

lemma T12_reach (a b : Fin 12) (h : adj12 a b = true) : T12.Reachable a b :=
  (T12_adj.mpr h).reachable

lemma T12_connected : T12.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨11, fun w => ?_⟩
  have r := T12_reach
  fin_cases w
  · exact (r 11 1 rfl).trans ((r 1 8 rfl).trans (r 8 0 rfl))
  · exact r 11 1 rfl
  · exact r 11 2 rfl
  · exact (r 11 2 rfl).trans ((r 2 9 rfl).trans (r 9 3 rfl))
  · exact (r 11 1 rfl).trans ((r 1 8 rfl).trans ((r 8 0 rfl).trans ((r 0 10 rfl).trans
      (r 10 4 rfl))))
  · exact (r 11 1 rfl).trans ((r 1 8 rfl).trans ((r 8 0 rfl).trans ((r 0 10 rfl).trans
      (r 10 5 rfl))))
  · exact r 11 6 rfl
  · exact r 11 7 rfl
  · exact (r 11 1 rfl).trans (r 1 8 rfl)
  · exact (r 11 2 rfl).trans (r 2 9 rfl)
  · exact (r 11 1 rfl).trans ((r 1 8 rfl).trans ((r 8 0 rfl).trans (r 0 10 rfl)))
  · exact Reachable.refl _

lemma T12_isTree : T12.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨T12_connected, ?_⟩
  have hs := T12.sum_degrees_eq_twice_card_edges
  have h22 : ∑ v, T12.degree v = 22 := by
    rw [Finset.sum_congr rfl fun v _ => T12_degree v]
    decide
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

lemma T12_dd : 4 ≤ dd T12 := by
  have h : univ.image (fun v => T12.degree v) = {1, 2, 3, 4} := by
    have e : (fun v => T12.degree v) = fun v => #(univ.filter (fun w => adj12 v w = true)) :=
      funext T12_degree
    rw [e]
    decide
  rw [dd, h]
  decide

lemma T12_mode (d : ℕ) :
    #(univ.filter fun v => T12.degree v = d) ≤ #(univ.filter fun v => T12.degree v = 2) := by
  simp only [T12_degree]
  have h : ∀ v : Fin 12, #(univ.filter (fun w => adj12 v w = true)) ≤ 4 := by decide
  have h5 : #(univ.filter fun v : Fin 12 => #(univ.filter (fun w => adj12 v w = true)) = 2) = 5 := by
    decide
  rw [h5]
  rcases Nat.lt_or_ge d 5 with hd | hd
  · interval_cases d <;> decide
  · have : univ.filter (fun v : Fin 12 => #(univ.filter (fun w => adj12 v w = true)) = d) = ∅ := by
      ext v; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      have := h v; omega
    rw [this]
    simp

lemma T12_totalDomNum : totalDomNum T12 ≤ 5 := by
  have hS : IsTDS T12 {0, 2, 9, 10, 11} := by
    have : ∀ v : Fin 12, ∃ u ∈ ({0, 2, 9, 10, 11} : Finset (Fin 12)), adj12 v u = true := by
      decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, T12_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({0, 2, 9, 10, 11} : Finset (Fin 12)) ∈
    {k | ∃ S, IsTDS T12 S ∧ #S = k})).trans card_le_five

/-- **WOWII Conjecture 367 is false** if "the most frequently occurring degree is two" allows
other degrees to occur equally often. -/
theorem not_conjecture367_ties :
    ¬ ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → 2 < Fintype.card V →
      (∀ d, #(univ.filter fun v => T.degree v = d) ≤ #(univ.filter fun v => T.degree v = 2)) →
      (4 / 3 : ℝ) * dd T ≤ totalDomNum T := by
  intro h
  have h12 := h (Fin 12) T12 T12_isTree (by decide) T12_mode
  have h1 : (4 : ℝ) ≤ dd T12 := by exact_mod_cast T12_dd
  have h2 : (totalDomNum T12 : ℝ) ≤ 5 := by exact_mod_cast T12_totalDomNum
  linarith

end WOWII367
