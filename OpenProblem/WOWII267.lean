import OpenProblem.WOWII378

/-!
# Written on the Wall II, Conjecture 267 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 267.** If `G` is a simple connected graph such that `girth(G) ≥ 5`, then
> `γ_t(G) ≥ CEIL[dist_avg(A, V)]`, where `A` is the set of minimum degree vertices.

Here `dist_avg(A, V)` is the mean of `d(a, v)` over `a ∈ A` and `v ∈ V`. We refute the
conjecture with or without the zero terms `d(a, a)` (`distAvgAV`, `distAvgAVPos`). We also refute
it whether trees count as having girth `∞` (Mathlib's `egirth`) or are excluded (Mathlib's
`girth`, which is `0` for acyclic graphs).

Trees violate the conjecture: the double star with `3` and `4` leaves has `γ_t = 2` and
`dist_avg(A, V) = 43/21`. Since trees might be excluded, the counterexample here has a cycle.

The counterexample `G22` has 22 vertices:

* the path `0 - 1 - 2 - 3 - 4 - 5`;
* a second path `1 - 6 - 7 - 4`, closing a 6-cycle;
* seven leaves `8, …, 14` at `0` and seven leaves `15, …, 21` at `5`.

Its girth is `6` and `{0, 1, 4, 5}` is a total dominating set, so `γ_t ≤ 4`. The minimum degree
vertices are the 14 leaves, and the distances from each leaf to all vertices sum to `89`. Hence
`dist_avg(A, V)` is `1246/308 > 4` with zero terms and `1246/294 > 4` without, and in both cases
its ceiling is at least `5`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII267

open SimpleGraph WOWII372

variable {V : Type*} [Fintype V]

/-! ### The invariants -/

/-- The set of vertices of minimum degree. -/
def minDegSet (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = G.minDegree

/-- `dist_avg(A, V)`: the mean of `d(a, v)` over all pairs `a ∈ A`, `v ∈ V`. -/
def distAvgAV (G : SimpleGraph V) (A : Finset V) : ℝ :=
  (∑ a ∈ A, ∑ v, (G.dist a v : ℝ)) / (#A * Fintype.card V)

/-- `dist_avg(A, V)` over the pairs `a ∈ A`, `v ≠ a`. The terms with `v = a` are zero, so the
numerator is the same as for `distAvgAV`. -/
def distAvgAVPos (G : SimpleGraph V) (A : Finset V) : ℝ :=
  (∑ a ∈ A, ∑ v, (G.dist a v : ℝ)) / (#A * (Fintype.card V - 1))

/-! ### Helper lemmas -/

omit [Fintype V] in
/-- A function growing by at most one along each edge bounds distances from below. -/
lemma le_add_dist {G : SimpleGraph V} (f : V → ℕ) (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    {u v : V} (hr : G.Reachable u v) : f v ≤ f u + G.dist u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp]
  clear hp hr
  induction p with
  | nil => simp
  | cons h q ih =>
    have := hf _ _ h
    rw [Walk.length_cons]
    omega

omit [Fintype V] in
/-- If every vertex other than `r` has a neighbour with smaller `f`, then `G` is connected. -/
lemma connected_of_parent {G : SimpleGraph V} (r : V) (f : V → ℕ) (par : V → V)
    (h : ∀ v, v ≠ r → G.Adj v (par v) ∧ f (par v) < f v) : G.Connected := by
  have hreach : ∀ k, ∀ v, f v = k → G.Reachable r v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      by_cases hvr : v = r
      · rw [hvr]
      · obtain ⟨hadj, hlt⟩ := h v hvr
        exact (ih (f (par v)) (by omega) (par v) rfl).trans hadj.symm.reachable
  have : Nonempty V := ⟨r⟩
  exact ⟨fun x y => (hreach _ x rfl).symm.trans (hreach _ y rfl)⟩

omit [Fintype V] in
/-- A graph without triangles and 4-cycles has extended girth at least `5`. -/
lemma five_le_egirth {G : SimpleGraph V} (h3 : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → b ≠ d → a = c) :
    5 ≤ G.egirth := by
  rw [le_egirth]
  intro a w hw
  have h3l := hw.three_le_length
  by_contra hlt
  have hlt' : w.length < 5 := by
    by_contra h
    exact hlt (by exact_mod_cast (not_lt.mp h))
  have hnd := hw.support_nodup
  cases w with
  | nil => simp at h3l
  | @cons _ b _ h1 w1 =>
    cases w1 with
    | nil => simp at h3l
    | @cons _ c _ h2 w2 =>
      cases w2 with
      | nil => simp at h3l
      | @cons _ d _ h3' w3 =>
        cases w3 with
        | nil => exact h3 _ _ _ h1 h2 h3'
        | @cons _ e _ h4' w4 =>
          cases w4 with
          | nil =>
            have hbd : b ≠ d := by
              rintro rfl
              simp at hnd
            have hca : c ≠ a := by
              rintro rfl
              simp at hnd
            exact hca (h4 _ _ _ _ h1 h2 h3' h4' hbd).symm
          | cons _ _ => simp at hlt'; omega

/-! ### The counterexample -/

/-- The edges of `G22`. -/
def E22 : List (Fin 22 × Fin 22) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 6), (6, 7), (4, 7),
    (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14),
    (5, 15), (5, 16), (5, 17), (5, 18), (5, 19), (5, 20), (5, 21)]

def adj22 (a b : Fin 22) : Bool := E22.contains (a, b) || E22.contains (b, a)

/-- A path `0 - … - 5` with a parallel path `1 - 6 - 7 - 4` and seven leaves at each end. -/
def G22 : SimpleGraph (Fin 22) := SimpleGraph.fromRel fun a b => adj22 a b = true

lemma G22_adj {a b : Fin 22} : G22.Adj a b ↔ adj22 a b = true := by
  have h : ∀ a b : Fin 22, (a ≠ b ∧ (adj22 a b = true ∨ adj22 b a = true)) ↔
      adj22 a b = true := by decide
  simpa [G22] using h a b

lemma G22_degree (v : Fin 22) : G22.degree v = #(univ.filter (fun w => adj22 v w = true)) :=
  WOWII378.degree_eq_card_filter G22 adj22 (fun _ _ => G22_adj) v

/-- Distances from `0` and from `5`. -/
def h0 : Fin 22 → ℕ := ![0, 1, 2, 3, 4, 5, 2, 3, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 6]
def h5 : Fin 22 → ℕ := ![5, 4, 3, 2, 1, 0, 3, 2, 6, 6, 6, 6, 6, 6, 6, 1, 1, 1, 1, 1, 1, 1]

/-- A neighbour one step closer to `0`. -/
def par22 : Fin 22 → Fin 22 := ![0, 0, 1, 2, 3, 4, 1, 6, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 5, 5, 5]

lemma G22_connected : G22.Connected := by
  refine connected_of_parent 0 h0 par22 fun v hv => ?_
  rw [G22_adj]
  revert v
  decide

lemma G22_card_edges : #G22.edgeFinset = 22 := by
  have hs := G22.sum_degrees_eq_twice_card_edges
  have h44 : ∑ v, G22.degree v = 44 := by
    rw [Finset.sum_congr rfl fun v _ => G22_degree v]
    decide
  omega

lemma G22_not_acyclic : ¬ G22.IsAcyclic := by
  intro h
  have hT : G22.IsTree := ⟨G22_connected, h⟩
  have := hT.card_edgeFinset
  rw [G22_card_edges, Fintype.card_fin] at this
  omega

lemma G22_egirth : 5 ≤ G22.egirth := by
  apply five_le_egirth
  · intro a b c hab hbc hca
    rw [G22_adj] at hab hbc hca
    have : ∀ a b c : Fin 22, adj22 a b = true → adj22 b c = true → adj22 c a = false := by decide
    rw [this a b c hab hbc] at hca
    exact Bool.false_ne_true hca
  · intro a b c d hab hbc hcd hda hbd
    rw [G22_adj] at hab hbc hcd hda
    by_contra hac
    have hcommon : ∀ a c : Fin 22, a ≠ c →
        #(univ.filter fun b => adj22 a b = true ∧ adj22 c b = true) ≤ 1 := by decide
    have hsub : ({b, d} : Finset (Fin 22)) ⊆
        univ.filter fun b => adj22 a b = true ∧ adj22 c b = true := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      have hcb : adj22 c b = true := by rw [← G22_adj] at hbc ⊢; exact hbc.symm
      have had : adj22 a d = true := by rw [← G22_adj] at hda ⊢; exact hda.symm
      rcases hx with rfl | rfl
      · exact mem_filter.mpr ⟨mem_univ _, hab, hcb⟩
      · exact mem_filter.mpr ⟨mem_univ _, had, hcd⟩
    have := (card_le_card hsub).trans (hcommon a c hac)
    rw [card_pair hbd] at this
    omega

lemma G22_girth : 5 ≤ G22.girth := by
  have h := ENat.toNat_le_toNat G22_egirth (egirth_eq_top.not.mpr G22_not_acyclic)
  simpa [girth] using h

lemma G22_minDegree : G22.minDegree = 1 := by
  apply le_antisymm
  · have : G22.degree 8 = 1 := by rw [G22_degree]; decide
    rw [← this]
    exact G22.minDegree_le_degree 8
  · apply le_minDegree_of_forall_le_degree
    intro v
    rw [G22_degree]
    revert v
    decide

/-- The leaves. -/
def A22 : Finset (Fin 22) := univ.filter fun v => 8 ≤ v.val

lemma G22_minDegSet : minDegSet G22 = A22 := by
  ext v
  simp only [minDegSet, A22, mem_filter, mem_univ, true_and, G22_minDegree, G22_degree]
  revert v
  decide

/-- The distances from a leaf `a`: `0` at `a` itself, and one more than the distance from its
support elsewhere. -/
def fLeaf (a v : Fin 22) : ℕ := if v = a then 0 else (if a.val ≤ 14 then h0 v else h5 v) + 1

lemma fLeaf_le_dist (a : Fin 22) (ha : a ∈ A22) (v : Fin 22) : fLeaf a v ≤ G22.dist a v := by
  have hlip : ∀ x y, G22.Adj x y → fLeaf a y ≤ fLeaf a x + 1 := by
    have : ∀ a ∈ A22, ∀ x y : Fin 22, adj22 x y = true → fLeaf a y ≤ fLeaf a x + 1 := by
      decide
    intro x y hxy
    exact this a ha x y (G22_adj.mp hxy)
  have h := le_add_dist (fLeaf a) hlip (G22_connected.preconnected a v)
  have h0 : fLeaf a a = 0 := by simp [fLeaf]
  omega

lemma sum_dist_ge : 1246 ≤ ∑ a ∈ A22, ∑ v, G22.dist a v := by
  have hsum : ∑ a ∈ A22, ∑ v, fLeaf a v = 1246 := by decide
  rw [← hsum]
  exact sum_le_sum fun a ha => sum_le_sum fun v _ => fLeaf_le_dist a ha v

lemma card_A22 : #A22 = 14 := by decide

lemma G22_totalDomNum : totalDomNum G22 ≤ 4 := by
  have hS : IsTDS G22 {0, 1, 4, 5} := by
    have : ∀ v : Fin 22, ∃ u ∈ ({0, 1, 4, 5} : Finset (Fin 22)), adj22 v u = true := by decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, G22_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({0, 1, 4, 5} : Finset (Fin 22)) ∈
    {k | ∃ S, IsTDS G22 S ∧ #S = k})).trans Finset.card_le_four

lemma four_lt_distAvgAV : 4 < distAvgAV G22 (minDegSet G22) := by
  rw [G22_minDegSet, distAvgAV, card_A22, Fintype.card_fin, lt_div_iff₀ (by norm_num)]
  have h := sum_dist_ge
  have h' : (1246 : ℝ) ≤ ∑ a ∈ A22, ∑ v, (G22.dist a v : ℝ) := by exact_mod_cast h
  norm_num
  linarith

lemma four_lt_distAvgAVPos : 4 < distAvgAVPos G22 (minDegSet G22) := by
  rw [G22_minDegSet, distAvgAVPos, card_A22, Fintype.card_fin, lt_div_iff₀ (by norm_num)]
  have h := sum_dist_ge
  have h' : (1246 : ℝ) ≤ ∑ a ∈ A22, ∑ v, (G22.dist a v : ℝ) := by exact_mod_cast h
  norm_num
  linarith

/-! ### The refutations -/

/-- The statement of Conjecture 267, for a girth condition and a reading of `dist_avg(A, V)`. -/
def Conjecture267 (girthOK : ∀ {V : Type} [Fintype V], SimpleGraph V → Prop)
    (avg : ∀ {V : Type} [Fintype V], SimpleGraph V → Finset V → ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → girthOK G →
    ⌈avg G (minDegSet G)⌉ ≤ (totalDomNum G : ℤ)

lemma not_conjecture267_of (girthOK : ∀ {V : Type} [Fintype V], SimpleGraph V → Prop)
    (avg : ∀ {V : Type} [Fintype V], SimpleGraph V → Finset V → ℝ) (hg : girthOK G22)
    (havg : 4 < avg G22 (minDegSet G22)) : ¬ Conjecture267 girthOK avg := by
  intro h
  have h1 : ⌈avg G22 (minDegSet G22)⌉ ≤ (totalDomNum G22 : ℤ) := h (Fin 22) G22 G22_connected hg
  have h2 : (4 : ℤ) < ⌈avg G22 (minDegSet G22)⌉ := Int.lt_ceil.mpr (by exact_mod_cast havg)
  have h3 : (totalDomNum G22 : ℤ) ≤ 4 := by exact_mod_cast G22_totalDomNum
  omega

/-- **WOWII Conjecture 267 is false** (girth in Mathlib's sense, mean over all `v ∈ V`). -/
theorem not_conjecture267 : ¬ Conjecture267 (fun G => 5 ≤ G.girth) distAvgAV :=
  not_conjecture267_of _ _ G22_girth four_lt_distAvgAV

/-- **WOWII Conjecture 267 is false** (girth in Mathlib's sense, mean over `v ≠ a`). -/
theorem not_conjecture267_pos : ¬ Conjecture267 (fun G => 5 ≤ G.girth) distAvgAVPos :=
  not_conjecture267_of _ _ G22_girth four_lt_distAvgAVPos

/-- **WOWII Conjecture 267 is false** (extended girth, trees allowed, mean over all `v ∈ V`). -/
theorem not_conjecture267_egirth : ¬ Conjecture267 (fun G => 5 ≤ G.egirth) distAvgAV :=
  not_conjecture267_of _ _ G22_egirth four_lt_distAvgAV

/-- **WOWII Conjecture 267 is false** (extended girth, trees allowed, mean over `v ≠ a`). -/
theorem not_conjecture267_egirth_pos : ¬ Conjecture267 (fun G => 5 ≤ G.egirth) distAvgAVPos :=
  not_conjecture267_of _ _ G22_egirth four_lt_distAvgAVPos

end WOWII267
