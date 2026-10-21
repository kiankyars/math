import OpenProblem.WOWII380

/-!
# Written on the Wall II, Conjectures 358 and 359 are false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 358.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ ½ ecc(C) + number of isolates of <S(T)>`,

> **Conjecture 359.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ ½ ecc(C) + number of components of <S(T) ∪ L>`,

where `C` is the center, `S(T)` the set of support vertices and `L` the set of leaves.

Both are false, whether `ecc(C)` is the eccentricity `max_v d(v, C)` of the center as a set or
the eccentricity of a center vertex (the radius). Every isolated support vertex together with its
leaves is a component of `<S(T) ∪ L>` (`card_isoSup_le`), so a counterexample to 358 is also one
to 359.

* `T19`: the path `3 - 13 - 2 - 17 - 11 - 0 - 15 - 6 - 16 - 1 - 12 - 18 - 4 - 14 - 5` with leaves
  `9, 7, 8, 10` attached at `17, 15, 16, 18`. The center is `{6}` with `ecc(C) = 7`. The six
  supports `13, 14, 15, 16, 17, 18` are pairwise non-adjacent, and `γ_t = 9 < 7/2 + 6`. It is the
  only counterexample on at most 19 vertices for the set reading. Attaching further pendant
  pairs along the path increases the gap without bound.
* `T12`: the path `2 - 8 - 1 - 10 - 0 - 7 - 11 - 3 - 9 - 4` with leaves `5, 6` at `10, 11`. Its
  radius is `5`, it has four isolated supports, and `γ_t = 6 < 5/2 + 4`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII358

open SimpleGraph WOWII372 WOWII377 WOWII378 WOWII380

variable {V : Type*} [Fintype V]

/-! ### Support vertices -/

/-- The leaves. -/
def leaves (T : SimpleGraph V) : Finset V := univ.filter fun v => T.degree v = 1

/-- The support vertices: vertices adjacent to a leaf. -/
def Sup (T : SimpleGraph V) : Finset V := univ.filter fun v => ∃ w, T.Adj v w ∧ T.degree w = 1

/-- The isolates of the subgraph induced by the support vertices. -/
def isoSup (T : SimpleGraph V) : Finset V :=
  (Sup T).filter fun v => ∀ w, T.Adj v w → w ∉ Sup T

/-- In a tree on at least three vertices, distinct isolated supports lie in distinct components of
`<S(T) ∪ L>`. -/
lemma card_isoSup_le {T : SimpleGraph V} (hT : T.IsTree) (hn : 3 ≤ Fintype.card V) :
    #(isoSup T) ≤ numComp T (Sup T ∪ leaves T) := by
  set K := Sup T ∪ leaves T
  set G' := T.induce (K : Set V)
  have hK : ∀ s ∈ isoSup T, s ∈ K := fun s hs => mem_union_left _ (mem_filter.mp hs).1
  let f : {s // s ∈ isoSup T} → G'.ConnectedComponent :=
    fun s => G'.connectedComponentMk ⟨s.1, hK s.1 s.2⟩
  have hf : Function.Injective f := by
    rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hr := ConnectedComponent.eq.mp h
    have hiso := (mem_filter.mp hs).2
    let C : Set (K : Set V) := {x | x.1 = s ∨ (T.Adj x.1 s ∧ T.degree x.1 = 1)}
    have hclosed : ∀ a b, G'.Adj a b → a ∈ C → b ∈ C := by
      intro a b hab ha
      have hab' : T.Adj a.1 b.1 := hab
      rcases ha with ha | ⟨has, hdeg⟩
      · have hbs : T.Adj b.1 s := ha ▸ hab'.symm
        have hbK := b.2
        rcases mem_union.mp (Finset.mem_coe.mp hbK) with hb | hb
        · exact absurd hb (hiso b.1 hbs.symm)
        · exact Or.inr ⟨hbs, (mem_filter.mp hb).2⟩
      · exact Or.inl (eq_of_degree_le_one (le_of_eq hdeg) hab' has)
    by_contra hne
    have : (⟨s', hK s' hs'⟩ : (K : Set V)) ∈ C := by
      by_contra hnot
      exact not_reachable_of_closed C (Or.inl rfl) hnot hclosed hr
    rcases this with h1 | ⟨hs's, hdeg'⟩
    · exact hne (Subtype.ext h1.symm)
    · -- then `s` and `s'` are adjacent leaves, so `T` has two vertices
      obtain ⟨ℓ, hℓ, hdℓ⟩ := (mem_filter.mp (mem_filter.mp hs').1).2
      have hℓs : ℓ = s := eq_of_degree_le_one (le_of_eq hdeg') hℓ hs's
      rw [hℓs] at hdℓ
      have hcl : ∀ u w, T.Adj u w → u ∈ ({s, s'} : Set V) → w ∈ ({s, s'} : Set V) := by
        intro u w huw hu
        rcases hu with rfl | rfl
        · exact Or.inr (eq_of_degree_le_one (le_of_eq hdℓ) huw hs's.symm)
        · exact Or.inl (eq_of_degree_le_one (le_of_eq hdeg') huw hs's)
      obtain ⟨z, hz⟩ : ∃ z, z ∉ ({s, s'} : Set V) := by
        by_contra hall
        push Not at hall
        have : #(univ : Finset V) ≤ #({s, s'} : Finset V) :=
          card_le_card fun x _ => by simpa using hall x
        rw [card_univ] at this
        have := card_le_two (a := s) (b := s')
        omega
      exact not_reachable_of_closed ({s, s'} : Set V) (by simp) hz hcl
        (hT.connected.preconnected s z)
  have : Finite G'.ConnectedComponent := Quot.finite _
  have := Nat.card_le_card_of_injective f hf
  simpa [numComp] using this

omit [Fintype V] in
/-- In a tree, a path realises the distance between its ends. -/
lemma dist_eq_length {T : SimpleGraph V} (hT : T.IsTree) {u v : V} (p : T.Walk u v)
    (hp : p.IsPath) : T.dist u v = p.length := by
  obtain ⟨q, hq⟩ := (hT.connected.preconnected u v).exists_walk_length_eq_dist
  have h1 : q.bypass.length ≤ q.length := q.length_bypass_le_length
  have h2 : q.bypass = p := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path u v).elim ⟨q.bypass, q.bypass_isPath⟩ ⟨p, hp⟩)
  rw [h2] at h1
  have := T.dist_le p
  omega

/-- The statement of Conjecture 358 with a reading `e` of `ecc(C)`. -/
def Conj358 (e : ∀ {V : Type} [Fintype V], SimpleGraph V → ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → 2 < Fintype.card V →
    (e T : ℝ) / 2 + #(isoSup T) ≤ totalDomNum T

/-- The statement of Conjecture 359 with a reading `e` of `ecc(C)`. -/
def Conj359 (e : ∀ {V : Type} [Fintype V], SimpleGraph V → ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → 2 < Fintype.card V →
    (e T : ℝ) / 2 + numComp T (Sup T ∪ leaves T) ≤ totalDomNum T

/-- A counterexample to 358 is a counterexample to 359. -/
lemma conj358_of_conj359 (e : ∀ {V : Type} [Fintype V], SimpleGraph V → ℕ) :
    Conj359 e → Conj358 e := by
  intro h V _ T hT hn
  have h1 := h V T hT hn
  have h2 : (#(isoSup T) : ℝ) ≤ numComp T (Sup T ∪ leaves T) := by
    exact_mod_cast card_isoSup_le hT hn
  linarith

/-! ### The 19-vertex tree -/

def E19 : List (Fin 19 × Fin 19) :=
  [(0, 11), (0, 15), (1, 12), (1, 16), (2, 13), (2, 17), (3, 13), (4, 14), (4, 18), (5, 14),
    (6, 15), (6, 16), (7, 15), (8, 16), (9, 17), (10, 18), (11, 17), (12, 18)]

def adj19 (a b : Fin 19) : Bool := E19.contains (a, b) || E19.contains (b, a)

def T19 : SimpleGraph (Fin 19) := SimpleGraph.fromRel fun a b => adj19 a b = true

lemma T19_adj {a b : Fin 19} : T19.Adj a b ↔ adj19 a b = true := by
  have h : ∀ a b : Fin 19,
      (a ≠ b ∧ (adj19 a b = true ∨ adj19 b a = true)) ↔ adj19 a b = true := by
    decide
  simpa [T19] using h a b

lemma h19 (a b : Fin 19) (h : adj19 a b = true) : T19.Adj a b := T19_adj.mpr h

lemma T19_degree (v : Fin 19) : T19.degree v = #(univ.filter (fun w => adj19 v w = true)) :=
  degree_eq_card_filter T19 adj19 (fun _ _ => T19_adj) v

lemma T19_connected : T19.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨6, fun w => ?_⟩
  fin_cases w
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) Walk.nil))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) Walk.nil))⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 2 rfl) Walk.nil)))))⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 2 rfl) (Walk.cons (h19 2 13 rfl) (Walk.cons (h19 13 3 rfl) Walk.nil)))))))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) Walk.nil)))))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) (Walk.cons (h19 4 14 rfl) (Walk.cons (h19 14 5 rfl) Walk.nil)))))))⟩
  · exact ⟨Walk.nil⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 7 rfl) Walk.nil))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 8 rfl) Walk.nil))⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 9 rfl) Walk.nil)))))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 10 rfl) Walk.nil)))))⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) Walk.nil)))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) Walk.nil)))⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 2 rfl) (Walk.cons (h19 2 13 rfl) Walk.nil))))))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) (Walk.cons (h19 4 14 rfl) Walk.nil))))))⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) Walk.nil)⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) Walk.nil)⟩
  · exact ⟨(Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) Walk.nil))))⟩
  · exact ⟨(Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) Walk.nil))))⟩

lemma T19_isTree : T19.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨T19_connected, ?_⟩
  have hs := T19.sum_degrees_eq_twice_card_edges
  have h36 : ∑ v, T19.degree v = 36 := by
    rw [Finset.sum_congr rfl fun v _ => T19_degree v]
    decide
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

lemma T19_Sup : Sup T19 = {13, 14, 15, 16, 17, 18} := by
  ext v
  simp only [Sup, mem_filter, mem_univ, true_and, T19_adj, T19_degree]
  revert v
  decide

lemma T19_isoSup : #(isoSup T19) = 6 := by
  have : isoSup T19 = {13, 14, 15, 16, 17, 18} := by
    ext v
    simp only [isoSup, mem_filter, T19_Sup, T19_adj]
    revert v
    decide
  rw [this]
  decide

lemma T19_totalDomNum : totalDomNum T19 ≤ 9 := by
  have hS : IsTDS T19 {2, 4, 6, 13, 14, 15, 16, 17, 18} := by
    have : ∀ v : Fin 19, ∃ u ∈ ({2, 4, 6, 13, 14, 15, 16, 17, 18} : Finset (Fin 19)),
        adj19 v u = true := by decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, T19_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({2, 4, 6, 13, 14, 15, 16, 17, 18} : Finset (Fin 19)) ∈
    {k | ∃ S, IsTDS T19 S ∧ #S = k})).trans (by decide)

lemma T19_ecc6 : ecc T19 6 ≤ 7 := by
  apply Finset.sup_le
  intro w _
  fin_cases w
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) Walk.nil))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) Walk.nil))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 2 rfl) Walk.nil)))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 2 rfl) (Walk.cons (h19 2 13 rfl) (Walk.cons (h19 13 3 rfl) Walk.nil)))))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) Walk.nil)))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) (Walk.cons (h19 4 14 rfl) (Walk.cons (h19 14 5 rfl) Walk.nil)))))))).trans (by simp)
  · exact (T19.dist_le Walk.nil).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 7 rfl) Walk.nil))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 8 rfl) Walk.nil))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 9 rfl) Walk.nil)))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 10 rfl) Walk.nil)))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) Walk.nil)))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) Walk.nil)))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) (Walk.cons (h19 17 2 rfl) (Walk.cons (h19 2 13 rfl) Walk.nil))))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) (Walk.cons (h19 4 14 rfl) Walk.nil))))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) Walk.nil)).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) Walk.nil)).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 15 rfl) (Walk.cons (h19 15 0 rfl) (Walk.cons (h19 0 11 rfl) (Walk.cons (h19 11 17 rfl) Walk.nil))))).trans (by simp)
  · exact (T19.dist_le (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) Walk.nil))))).trans (by simp)

lemma T19_dist35 : T19.dist 3 5 = 14 := by
  have hp : ((Walk.cons (h19 3 13 rfl) (Walk.cons (h19 13 2 rfl) (Walk.cons (h19 2 17 rfl) (Walk.cons (h19 17 11 rfl) (Walk.cons (h19 11 0 rfl) (Walk.cons (h19 0 15 rfl) (Walk.cons (h19 15 6 rfl) (Walk.cons (h19 6 16 rfl) (Walk.cons (h19 16 1 rfl) (Walk.cons (h19 1 12 rfl) (Walk.cons (h19 12 18 rfl) (Walk.cons (h19 18 4 rfl) (Walk.cons (h19 4 14 rfl) (Walk.cons (h19 14 5 rfl) Walk.nil))))))))))))))).IsPath := by
    rw [Walk.isPath_def]
    decide
  rw [dist_eq_length T19_isTree _ hp]
  rfl

lemma T19_eccSet : 7 ≤ eccSet T19 (WOWII380.center T19) := by
  have hconn := T19_connected
  obtain ⟨c0, hc0⟩ := WOWII380.center_nonempty T19
  have hne : ((fun a => T19.dist 3 a) '' (WOWII380.center T19 : Set (Fin 19))).Nonempty :=
    ⟨_, c0, Finset.mem_coe.mpr hc0, rfl⟩
  obtain ⟨c, hc, hcd⟩ := Nat.sInf_mem hne
  have hcd' : T19.dist 3 c = distToSet T19 3 (WOWII380.center T19) := hcd
  have hrad : ecc T19 c ≤ 7 := by
    rw [(mem_filter.mp (Finset.mem_coe.mp hc)).2]
    exact (rad_le_ecc T19 6).trans T19_ecc6
  have h5 := dist_le_ecc T19 c 5
  have htri := hconn.dist_triangle (u := 3) (v := c) (w := 5)
  rw [T19_dist35] at htri
  have : 7 ≤ distToSet T19 3 (WOWII380.center T19) := by omega
  exact this.trans (Finset.le_sup (f := fun v => distToSet T19 v (WOWII380.center T19)) (mem_univ 3))

/-! ### The 12-vertex tree -/

def E12 : List (Fin 12 × Fin 12) :=
  [(0, 7), (0, 10), (1, 8), (1, 10), (2, 8), (3, 9), (3, 11), (4, 9), (5, 10), (6, 11), (7, 11)]

def adj12 (a b : Fin 12) : Bool := E12.contains (a, b) || E12.contains (b, a)

def T12 : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adj12 a b = true

lemma T12_adj {a b : Fin 12} : T12.Adj a b ↔ adj12 a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adj12 a b = true ∨ adj12 b a = true)) ↔ adj12 a b = true := by
    decide
  simpa [T12] using h a b

lemma h12 (a b : Fin 12) (h : adj12 a b = true) : T12.Adj a b := T12_adj.mpr h

lemma T12_degree (v : Fin 12) : T12.degree v = #(univ.filter (fun w => adj12 v w = true)) :=
  degree_eq_card_filter T12 adj12 (fun _ _ => T12_adj) v

lemma T12_connected : T12.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  have r := fun a b h => (h12 a b h).reachable
  fin_cases w
  · exact Reachable.refl _
  · exact (r 0 10 rfl).trans (r 10 1 rfl)
  · exact (r 0 10 rfl).trans ((r 10 1 rfl).trans ((r 1 8 rfl).trans (r 8 2 rfl)))
  · exact (r 0 7 rfl).trans ((r 7 11 rfl).trans (r 11 3 rfl))
  · exact (r 0 7 rfl).trans ((r 7 11 rfl).trans ((r 11 3 rfl).trans ((r 3 9 rfl).trans
      (r 9 4 rfl))))
  · exact (r 0 10 rfl).trans (r 10 5 rfl)
  · exact (r 0 7 rfl).trans ((r 7 11 rfl).trans (r 11 6 rfl))
  · exact r 0 7 rfl
  · exact (r 0 10 rfl).trans ((r 10 1 rfl).trans (r 1 8 rfl))
  · exact (r 0 7 rfl).trans ((r 7 11 rfl).trans ((r 11 3 rfl).trans (r 3 9 rfl)))
  · exact r 0 10 rfl
  · exact (r 0 7 rfl).trans (r 7 11 rfl)

lemma T12_isTree : T12.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨T12_connected, ?_⟩
  have hs := T12.sum_degrees_eq_twice_card_edges
  have h22 : ∑ v, T12.degree v = 22 := by
    rw [Finset.sum_congr rfl fun v _ => T12_degree v]
    decide
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

lemma T12_Sup : Sup T12 = {8, 9, 10, 11} := by
  ext v
  simp only [Sup, mem_filter, mem_univ, true_and, T12_adj, T12_degree]
  revert v
  decide

lemma T12_isoSup : #(isoSup T12) = 4 := by
  have : isoSup T12 = {8, 9, 10, 11} := by
    ext v
    simp only [isoSup, mem_filter, T12_Sup, T12_adj]
    revert v
    decide
  rw [this]
  decide

lemma T12_totalDomNum : totalDomNum T12 ≤ 6 := by
  have hS : IsTDS T12 {1, 3, 8, 9, 10, 11} := by
    have : ∀ v : Fin 12, ∃ u ∈ ({1, 3, 8, 9, 10, 11} : Finset (Fin 12)), adj12 v u = true := by
      decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, T12_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({1, 3, 8, 9, 10, 11} : Finset (Fin 12)) ∈
    {k | ∃ S, IsTDS T12 S ∧ #S = k})).trans (by decide)

lemma T12_rad : 5 ≤ rad T12 := by
  have hp : ((Walk.cons (h12 2 8 rfl) (Walk.cons (h12 8 1 rfl) (Walk.cons (h12 1 10 rfl) (Walk.cons (h12 10 0 rfl) (Walk.cons (h12 0 7 rfl) (Walk.cons (h12 7 11 rfl) (Walk.cons (h12 11 3 rfl) (Walk.cons (h12 3 9 rfl) (Walk.cons (h12 9 4 rfl) Walk.nil)))))))))).IsPath := by
    rw [Walk.isPath_def]
    decide
  have h24 : T12.dist 2 4 = 9 := by rw [dist_eq_length T12_isTree _ hp]; rfl
  obtain ⟨v, hv⟩ := Nat.sInf_mem (Set.range_nonempty (ecc T12))
  have h1 := dist_le_ecc T12 v 2
  have h2 := dist_le_ecc T12 v 4
  have htri := T12_connected.dist_triangle (u := 2) (v := v) (w := 4)
  rw [h24, T12.dist_comm] at htri
  unfold rad
  rw [← hv]
  omega

/-! ### The refutations -/

/-- **WOWII Conjecture 358 is false** with `ecc(C) = max_v d(v, C)`. -/
theorem not_conjecture358 : ¬ Conj358 fun T => eccSet T (WOWII380.center T) := by
  intro h
  have h19 := h (Fin 19) T19 T19_isTree (by decide)
  have h1 : (7 : ℝ) ≤ eccSet T19 (WOWII380.center T19) := by exact_mod_cast T19_eccSet
  have h2 : (#(isoSup T19) : ℝ) = 6 := by exact_mod_cast T19_isoSup
  have h3 : (totalDomNum T19 : ℝ) ≤ 9 := by exact_mod_cast T19_totalDomNum
  simp only at h19
  linarith

/-- **WOWII Conjecture 359 is false** with `ecc(C) = max_v d(v, C)`. -/
theorem not_conjecture359 : ¬ Conj359 fun T => eccSet T (WOWII380.center T) :=
  fun h => not_conjecture358 (conj358_of_conj359 _ h)

/-- **WOWII Conjecture 358 is false** with `ecc(C)` the radius. -/
theorem not_conjecture358_rad : ¬ Conj358 fun T => rad T := by
  intro h
  have h12 := h (Fin 12) T12 T12_isTree (by decide)
  have h1 : (5 : ℝ) ≤ rad T12 := by exact_mod_cast T12_rad
  have h2 : (#(isoSup T12) : ℝ) = 4 := by exact_mod_cast T12_isoSup
  have h3 : (totalDomNum T12 : ℝ) ≤ 6 := by exact_mod_cast T12_totalDomNum
  simp only at h12
  linarith

/-- **WOWII Conjecture 359 is false** with `ecc(C)` the radius. -/
theorem not_conjecture359_rad : ¬ Conj359 fun T => rad T :=
  fun h => not_conjecture358_rad (conj358_of_conj359 _ h)

end WOWII358
