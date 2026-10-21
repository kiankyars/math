import OpenProblem.WOWII348
import OpenProblem.WOWII377

/-!
# Written on the Wall II, Conjecture 378 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 378.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ number of components of <M> + dist_avg(D_2(T))`.

Here `M` is the set of vertices of maximum degree and `D_2(T)` the set of vertices of degree two.
The page does not define `dist_avg(S)` for a set `S`, and several readings are in use. We refute
the conjecture under each of the following:

* `distAvgPairs`: the mean distance over ordered pairs of distinct vertices of `S`, matching
  `dist_avg(V)` for the average distance of a graph (and `distAvgSet` in formal-conjectures);
* `distAvgToSet`: the mean of `d(v, S)` over all vertices `v`;
* `distAvgToSetPos`: the mean of `d(v, S)` over the vertices `v ∉ S`;
* `distAvgFrom`: the mean of `d(s, v)` over pairs `s ∈ S`, `v ≠ s`.

For the first reading, the counterexample is the 9-vertex tree `T9`. It is the path
`5 - 0 - 7 - 2 - 8 - 1 - 6` with an extra leaf `3` at `7` and an extra leaf `4` at `8`. Here
`γ_t = 4` while `<M>` has two components and `dist_avg(D_2) = 8/3`.

For the other three, the counterexample is the spider `T5` with legs of lengths `1, 1, 2`. Here
`γ_t = 2`, `<M>` has one component, and the three averages are `6/5`, `3/2` and `3/2`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII378

open SimpleGraph WOWII372 WOWII377

variable {V : Type*} [Fintype V]

/-! ### The invariants -/

/-- The number of connected components of the subgraph induced by `A`. -/
def numComp (T : SimpleGraph V) (A : Finset V) : ℕ :=
  Nat.card (T.induce (A : Set V)).ConnectedComponent

/-- The ordered pairs of distinct vertices of `A`. -/
def pairs (A : Finset V) : Finset (V × V) := (A ×ˢ A).filter (fun p => p.1 ≠ p.2)

/-- Mean distance over ordered pairs of distinct vertices of `A`. -/
def distAvgPairs (T : SimpleGraph V) (A : Finset V) : ℝ :=
  (∑ p ∈ pairs A, (T.dist p.1 p.2 : ℝ)) / #(pairs A)

/-- The distance from `v` to the set `A`. -/
def distToSet (T : SimpleGraph V) (v : V) (A : Finset V) : ℕ :=
  sInf ((fun a => T.dist v a) '' (A : Set V))

/-- Mean of `d(v, A)` over all vertices. -/
def distAvgToSet (T : SimpleGraph V) (A : Finset V) : ℝ :=
  (∑ v, (distToSet T v A : ℝ)) / Fintype.card V

/-- Mean of `d(v, A)` over the vertices outside `A`. -/
def distAvgToSetPos (T : SimpleGraph V) (A : Finset V) : ℝ :=
  (∑ v ∈ Aᶜ, (distToSet T v A : ℝ)) / #Aᶜ

/-- Mean of `d(a, v)` over pairs with `a ∈ A` and `v ≠ a`. -/
def distAvgFrom (T : SimpleGraph V) (A : Finset V) : ℝ :=
  (∑ p ∈ (A ×ˢ univ).filter (fun p => p.1 ≠ p.2), (T.dist p.1 p.2 : ℝ)) /
    #((A ×ˢ univ).filter (fun p => p.1 ≠ p.2))

/-- The statement of Conjecture 378 for a reading `avg` of `dist_avg`. -/
def Conjecture378 (avg : ∀ {V : Type} [Fintype V], SimpleGraph V → Finset V → ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → 2 < Fintype.card V →
    (numComp T (maxDegSet T) : ℝ) + avg T (WOWII348.D2 T) ≤ totalDomNum T

/-! ### Helper lemmas -/

omit [Fintype V] in
lemma two_le_dist {G : SimpleGraph V} {u v : V} (hr : G.Reachable u v) (hne : u ≠ v)
    (hadj : ¬ G.Adj u v) : 2 ≤ G.dist u v := by
  have h0 : G.dist u v ≠ 0 := fun h => hne (hr.dist_eq_zero_iff.mp h)
  have h1 : G.dist u v ≠ 1 := fun h => hadj (dist_eq_one_iff_adj.mp h)
  omega

omit [Fintype V] in
lemma three_le_dist {G : SimpleGraph V} {u v : V} (hr : G.Reachable u v) (hne : u ≠ v)
    (hadj : ¬ G.Adj u v) (hw : ∀ w, G.Adj u w → ¬ G.Adj w v) : 3 ≤ G.dist u v := by
  have h2 := two_le_dist hr hne hadj
  by_contra h
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hp2 : p.length = 2 := by omega
  cases p with
  | nil => simp at hp2
  | cons h1 q =>
    cases q with
    | nil => simp at hp2
    | cons h2 q' =>
      cases q' with
      | nil => exact hw _ h1 h2
      | cons _ _ => simp at hp2

lemma degree_eq_card_filter (G : SimpleGraph V) (f : V → V → Bool)
    (hG : ∀ a b, G.Adj a b ↔ f a b = true) (v : V) :
    G.degree v = #(univ.filter (fun w => f v w = true)) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [hG]

omit [Fintype V] in
lemma distToSet_singleton (T : SimpleGraph V) (v a : V) : distToSet T v {a} = T.dist v a := by
  simp [distToSet]

lemma one_le_numComp (T : SimpleGraph V) {A : Finset V} {a : V} (ha : a ∈ A) :
    1 ≤ numComp T A := by
  have : Nonempty (T.induce (A : Set V)).ConnectedComponent :=
    ⟨(T.induce (A : Set V)).connectedComponentMk ⟨a, ha⟩⟩
  have : Finite (T.induce (A : Set V)).ConnectedComponent := Quot.finite _
  exact Nat.card_pos

/-! ### The 9-vertex tree -/

/-- The edges of `T9`. -/
def E9 : List (Fin 9 × Fin 9) := [(0, 5), (0, 7), (1, 6), (1, 8), (2, 7), (2, 8), (3, 7), (4, 8)]

def adj9 (a b : Fin 9) : Bool := E9.contains (a, b) || E9.contains (b, a)

/-- The path `5 - 0 - 7 - 2 - 8 - 1 - 6` with a leaf `3` at `7` and a leaf `4` at `8`. -/
def T9 : SimpleGraph (Fin 9) := SimpleGraph.fromRel fun a b => adj9 a b = true

lemma T9_adj {a b : Fin 9} : T9.Adj a b ↔ adj9 a b = true := by
  have h : ∀ a b : Fin 9, (a ≠ b ∧ (adj9 a b = true ∨ adj9 b a = true)) ↔ adj9 a b = true := by
    decide
  simpa [T9] using h a b

lemma T9_degree (v : Fin 9) : T9.degree v = #(univ.filter (fun w => adj9 v w = true)) :=
  degree_eq_card_filter T9 adj9 (fun _ _ => T9_adj) v

lemma T9_reach (a b : Fin 9) (h : adj9 a b = true) : T9.Reachable a b := (T9_adj.mpr h).reachable

lemma T9_connected : T9.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨7, fun w => ?_⟩
  fin_cases w
  · exact T9_reach 7 0 rfl
  · exact (T9_reach 7 2 rfl).trans ((T9_reach 2 8 rfl).trans (T9_reach 8 1 rfl))
  · exact T9_reach 7 2 rfl
  · exact T9_reach 7 3 rfl
  · exact (T9_reach 7 2 rfl).trans ((T9_reach 2 8 rfl).trans (T9_reach 8 4 rfl))
  · exact (T9_reach 7 0 rfl).trans (T9_reach 0 5 rfl)
  · exact (T9_reach 7 2 rfl).trans ((T9_reach 2 8 rfl).trans
      ((T9_reach 8 1 rfl).trans (T9_reach 1 6 rfl)))
  · exact Reachable.refl _
  · exact (T9_reach 7 2 rfl).trans (T9_reach 2 8 rfl)

lemma T9_isTree : T9.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨T9_connected, ?_⟩
  have hs := T9.sum_degrees_eq_twice_card_edges
  have h16 : ∑ v, T9.degree v = 16 := by
    rw [Finset.sum_congr rfl fun v _ => T9_degree v]
    decide
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

lemma T9_maxDegree : T9.maxDegree = 3 := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rw [T9_degree]
    revert v
    decide
  · have : T9.degree 7 = 3 := by rw [T9_degree]; decide
    rw [← this]
    exact T9.degree_le_maxDegree 7

lemma T9_maxDegSet : maxDegSet T9 = {7, 8} := by
  ext v
  simp only [maxDegSet, mem_filter, mem_univ, true_and, T9_maxDegree, T9_degree]
  revert v
  decide

lemma T9_D2 : WOWII348.D2 T9 = {0, 1, 2} := by
  ext v
  simp only [WOWII348.D2, mem_filter, mem_univ, true_and, T9_degree]
  revert v
  decide

lemma T9_totalDomNum : totalDomNum T9 ≤ 4 := by
  have hS : IsTDS T9 {0, 1, 7, 8} := by
    have : ∀ v : Fin 9, ∃ u ∈ ({0, 1, 7, 8} : Finset (Fin 9)), adj9 v u = true := by decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, T9_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({0, 1, 7, 8} : Finset (Fin 9)) ∈
    {k | ∃ S, IsTDS T9 S ∧ #S = k})).trans Finset.card_le_four

lemma T9_numComp : 2 ≤ numComp T9 (maxDegSet T9) := by
  set K := T9.induce ((maxDegSet T9 : Finset (Fin 9)) : Set (Fin 9))
  have h7 : (7 : Fin 9) ∈ maxDegSet T9 := by rw [T9_maxDegSet]; decide
  have h8 : (8 : Fin 9) ∈ maxDegSet T9 := by rw [T9_maxDegSet]; decide
  let a : (maxDegSet T9 : Set (Fin 9)) := ⟨7, h7⟩
  let b : (maxDegSet T9 : Set (Fin 9)) := ⟨8, h8⟩
  have hnr : ¬ K.Reachable a b := by
    refine not_reachable_of_closed {a} rfl (by simp [a, b]) ?_
    intro x y hxy hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hmem : ∀ z : Fin 9, z ∈ maxDegSet T9 → z = 7 ∨ z = 8 := by
      intro z hz
      rw [T9_maxDegSet] at hz
      simpa using hz
    have hy := hmem y.1 y.2
    have hadj : adj9 7 y.1 = true := T9_adj.mp hxy
    exfalso
    revert hadj hy
    generalize y.1 = z
    revert z
    decide
  have : Finite K.ConnectedComponent := Quot.finite _
  have hinj : Function.Injective
      (![K.connectedComponentMk a, K.connectedComponentMk b] : Fin 2 → K.ConnectedComponent) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (ConnectedComponent.eq.mp hij) hnr
    · exact absurd (ConnectedComponent.eq.mp hij).symm hnr
    · rfl
  have := Nat.card_le_card_of_injective _ hinj
  simpa [numComp, K] using this

lemma T9_pairs : pairs ({0, 1, 2} : Finset (Fin 9)) =
    {(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)} := by
  ext ⟨a, b⟩
  simp only [pairs, mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
  revert a b
  decide

lemma T9_distAvgPairs : 14 / 6 ≤ distAvgPairs T9 (WOWII348.D2 T9) := by
  rw [T9_D2, distAvgPairs, T9_pairs]
  have hr : ∀ u v : Fin 9, T9.Reachable u v := T9_connected.preconnected
  have hw : ∀ w : Fin 9, adj9 0 w = true → ¬ adj9 w 1 = true := by decide
  have hw' : ∀ w : Fin 9, adj9 1 w = true → ¬ adj9 w 0 = true := by decide
  have d01 : 3 ≤ T9.dist 0 1 := three_le_dist (hr 0 1) (by decide) (by rw [T9_adj]; decide)
    (fun w h h' => hw w (T9_adj.mp h) (T9_adj.mp h'))
  have d10 : 3 ≤ T9.dist 1 0 := three_le_dist (hr 1 0) (by decide) (by rw [T9_adj]; decide)
    (fun w h h' => hw' w (T9_adj.mp h) (T9_adj.mp h'))
  have d02 : 2 ≤ T9.dist 0 2 := two_le_dist (hr 0 2) (by decide) (by rw [T9_adj]; decide)
  have d20 : 2 ≤ T9.dist 2 0 := two_le_dist (hr 2 0) (by decide) (by rw [T9_adj]; decide)
  have d12 : 2 ≤ T9.dist 1 2 := two_le_dist (hr 1 2) (by decide) (by rw [T9_adj]; decide)
  have d21 : 2 ≤ T9.dist 2 1 := two_le_dist (hr 2 1) (by decide) (by rw [T9_adj]; decide)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have hc : #({(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)} : Finset (Fin 9 × Fin 9)) = 6 := by
    decide
  rw [hc]
  have : (14 : ℝ) ≤ (T9.dist 0 1 : ℝ) + (T9.dist 0 2 + (T9.dist 1 0 + (T9.dist 1 2 +
      (T9.dist 2 0 + T9.dist 2 1)))) := by
    exact_mod_cast (by omega : 14 ≤ T9.dist 0 1 + (T9.dist 0 2 + (T9.dist 1 0 + (T9.dist 1 2 +
      (T9.dist 2 0 + T9.dist 2 1)))))
  dsimp only
  push_cast
  gcongr

/-- **WOWII Conjecture 378 is false** when `dist_avg(S)` is the mean distance over ordered pairs of
distinct vertices of `S`. -/
theorem not_conjecture378_pairs : ¬ Conjecture378 distAvgPairs := by
  intro h
  have h9 := h (Fin 9) T9 T9_isTree (by decide)
  have h1 : (2 : ℝ) ≤ numComp T9 (maxDegSet T9) := by exact_mod_cast T9_numComp
  have h2 := T9_distAvgPairs
  have h3 : (totalDomNum T9 : ℝ) ≤ 4 := by exact_mod_cast T9_totalDomNum
  linarith

/-! ### The spider with legs `1, 1, 2` -/

/-- The edges of `T5`. -/
def E5 : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (3, 4)]

def adj5 (a b : Fin 5) : Bool := E5.contains (a, b) || E5.contains (b, a)

/-- The spider with centre `0` and legs `0 - 1`, `0 - 2` and `0 - 3 - 4`. -/
def T5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun a b => adj5 a b = true

lemma T5_adj {a b : Fin 5} : T5.Adj a b ↔ adj5 a b = true := by
  have h : ∀ a b : Fin 5, (a ≠ b ∧ (adj5 a b = true ∨ adj5 b a = true)) ↔ adj5 a b = true := by
    decide
  simpa [T5] using h a b

lemma T5_degree (v : Fin 5) : T5.degree v = #(univ.filter (fun w => adj5 v w = true)) :=
  degree_eq_card_filter T5 adj5 (fun _ _ => T5_adj) v

lemma T5_reach (a b : Fin 5) (h : adj5 a b = true) : T5.Reachable a b := (T5_adj.mpr h).reachable

lemma T5_connected : T5.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  fin_cases w
  · exact Reachable.refl _
  · exact T5_reach 0 1 rfl
  · exact T5_reach 0 2 rfl
  · exact T5_reach 0 3 rfl
  · exact (T5_reach 0 3 rfl).trans (T5_reach 3 4 rfl)

lemma T5_isTree : T5.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨T5_connected, ?_⟩
  have hs := T5.sum_degrees_eq_twice_card_edges
  have h8 : ∑ v, T5.degree v = 8 := by
    rw [Finset.sum_congr rfl fun v _ => T5_degree v]
    decide
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

lemma T5_maxDegree : T5.maxDegree = 3 := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rw [T5_degree]
    revert v
    decide
  · have : T5.degree 0 = 3 := by rw [T5_degree]; decide
    rw [← this]
    exact T5.degree_le_maxDegree 0

lemma T5_D2 : WOWII348.D2 T5 = {3} := by
  ext v
  simp only [WOWII348.D2, mem_filter, mem_univ, true_and, T5_degree]
  revert v
  decide

lemma T5_numComp : 1 ≤ numComp T5 (maxDegSet T5) := by
  apply one_le_numComp T5 (a := 0)
  simp only [maxDegSet, mem_filter, mem_univ, true_and, T5_maxDegree, T5_degree]
  decide

lemma T5_totalDomNum : totalDomNum T5 ≤ 2 := by
  have hS : IsTDS T5 {0, 3} := by
    have : ∀ v : Fin 5, ∃ u ∈ ({0, 3} : Finset (Fin 5)), adj5 v u = true := by decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, T5_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({0, 3} : Finset (Fin 5)) ∈
    {k | ∃ S, IsTDS T5 S ∧ #S = k})).trans Finset.card_le_two

/-- The distances to `3` in `T5` sum to at least `6`. -/
lemma T5_sum_dist : (6 : ℝ) ≤ ∑ v, (T5.dist v 3 : ℝ) := by
  have hr : ∀ u w : Fin 5, T5.Reachable u w := T5_connected.preconnected
  have d0 : 0 < T5.dist 0 3 := (hr 0 3).pos_dist_of_ne (by decide)
  have d1 : 2 ≤ T5.dist 1 3 := two_le_dist (hr 1 3) (by decide) (by rw [T5_adj]; decide)
  have d2 : 2 ≤ T5.dist 2 3 := two_le_dist (hr 2 3) (by decide) (by rw [T5_adj]; decide)
  have d4 : 0 < T5.dist 4 3 := (hr 4 3).pos_dist_of_ne (by decide)
  rw [Fin.sum_univ_five]
  have : (6 : ℝ) ≤ (T5.dist 0 3 : ℝ) + T5.dist 1 3 + T5.dist 2 3 + T5.dist 3 3 + T5.dist 4 3 := by
    exact_mod_cast (by omega : 6 ≤ T5.dist 0 3 + T5.dist 1 3 + T5.dist 2 3 + T5.dist 3 3 +
      T5.dist 4 3)
  simpa using this

/-- **WOWII Conjecture 378 is false** when `dist_avg(S)` is the mean of `d(v, S)` over all `v`. -/
theorem not_conjecture378_toSet : ¬ Conjecture378 distAvgToSet := by
  intro h
  have h5 := h (Fin 5) T5 T5_isTree (by decide)
  have h1 : (1 : ℝ) ≤ numComp T5 (maxDegSet T5) := by exact_mod_cast T5_numComp
  have h3 : (totalDomNum T5 : ℝ) ≤ 2 := by exact_mod_cast T5_totalDomNum
  have h2 : (6 / 5 : ℝ) ≤ distAvgToSet T5 (WOWII348.D2 T5) := by
    rw [T5_D2, distAvgToSet, Fintype.card_fin]
    simp only [distToSet_singleton]
    have hs := T5_sum_dist
    push_cast
    gcongr
  linarith

/-- **WOWII Conjecture 378 is false** when `dist_avg(S)` is the mean of `d(v, S)` over `v ∉ S`. -/
theorem not_conjecture378_toSetPos : ¬ Conjecture378 distAvgToSetPos := by
  intro h
  have h5 := h (Fin 5) T5 T5_isTree (by decide)
  have h1 : (1 : ℝ) ≤ numComp T5 (maxDegSet T5) := by exact_mod_cast T5_numComp
  have h3 : (totalDomNum T5 : ℝ) ≤ 2 := by exact_mod_cast T5_totalDomNum
  have h2 : (6 / 4 : ℝ) ≤ distAvgToSetPos T5 (WOWII348.D2 T5) := by
    rw [T5_D2, distAvgToSetPos]
    simp only [distToSet_singleton]
    have hs := T5_sum_dist
    have hsplit := Finset.sum_compl_add_sum ({3} : Finset (Fin 5)) (fun v => (T5.dist v 3 : ℝ))
    rw [Finset.sum_singleton, SimpleGraph.dist_self, Nat.cast_zero, add_zero] at hsplit
    have hc : #({3} : Finset (Fin 5))ᶜ = 4 := by decide
    have key : (6 / 4 : ℝ) ≤ (∑ x ∈ ({3} : Finset (Fin 5))ᶜ, (T5.dist x 3 : ℝ)) /
        (#({3} : Finset (Fin 5))ᶜ : ℝ) := by
      rw [hsplit, hc]
      push_cast
      gcongr
    convert key using 3
    all_goals first | (ext; simp) | (congr 1; ext; simp)
  linarith

/-- **WOWII Conjecture 378 is false** when `dist_avg(S)` is the mean of `d(s, v)` over pairs with
`s ∈ S` and `v ≠ s`. -/
theorem not_conjecture378_from : ¬ Conjecture378 distAvgFrom := by
  intro h
  have h5 := h (Fin 5) T5 T5_isTree (by decide)
  have h1 : (1 : ℝ) ≤ numComp T5 (maxDegSet T5) := by exact_mod_cast T5_numComp
  have h3 : (totalDomNum T5 : ℝ) ≤ 2 := by exact_mod_cast T5_totalDomNum
  have h2 : (6 / 4 : ℝ) ≤ distAvgFrom T5 (WOWII348.D2 T5) := by
    rw [T5_D2, distAvgFrom, Finset.sum_filter, Finset.card_filter, Finset.sum_product,
      Finset.sum_product, Finset.sum_singleton, Finset.sum_singleton]
    have hs := T5_sum_dist
    have hsymm : ∑ v, (T5.dist v 3 : ℝ) = ∑ v, (T5.dist 3 v : ℝ) :=
      Finset.sum_congr rfl fun v _ => by rw [SimpleGraph.dist_comm]
    rw [hsymm, Fin.sum_univ_five] at hs
    simp only [Fin.sum_univ_five, Fin.isValue, ne_eq]
    simp only [show ¬ ((3 : Fin 5) = 0) from by decide, show ¬ ((3 : Fin 5) = 1) from by decide,
      show ¬ ((3 : Fin 5) = 2) from by decide, show ¬ ((3 : Fin 5) = 4) from by decide,
      not_false_eq_true, not_true_eq_false, ite_true, ite_false, SimpleGraph.dist_self] at hs ⊢
    push_cast at hs ⊢
    linarith
  linarith

end WOWII378
