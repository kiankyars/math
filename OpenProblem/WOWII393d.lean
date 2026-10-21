import OpenProblem.WOWII402
import OpenProblem.WOWII422b
import OpenProblem.WOWII444
import OpenProblem.WOWII326

/-!
# Written on the Wall II, Conjecture 393d is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 393d.** If `G` is a connected graph on `n > 2` vertices, then
> `γ_2 ≤ μ(G[V - N(N(P))]) + α(G[V - M]) + |M_4|`, where `P` is the set of pendants, `M` is the
> set of maximum degree vertices and `M_4` is the set of vertices each of which is incident with
> the maximum number of `K_4`.

Here `γ_2` is the 2-domination number, `μ` the matching number and `α` the independence number.

The counterexample `G` has 12 vertices and 26 edges and was found by simulated annealing.

* The pendants are `4` and `5`, attached to `6` and `9`. Then `V - N(N(P)) = {3, 6, 9, 11}` is
  independent, so `μ(G[V - N(N(P))]) = 0`.
* The maximum degree `6` is attained at `M = {1, 2, 7, 10}`. The other eight vertices are
  covered by the edges `0-3, 4-6, 5-9, 8-11`, so `α(G[V - M]) ≤ 4`.
* Vertex `2` lies in four copies of `K_4` and every other vertex in fewer, so `|M_4| = 1`.

So the bound is at most `5`. But `γ_2 = 6`. A 2-dominating set contains the pendants `4` and
`5`, and a finite check shows that no three further vertices complete it.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII393d

open WOWII382b WOWII326 WOWII422b WOWII444

variable {V : Type*} [Fintype V]

/-- The pendant vertices. -/
def pend (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = 1

/-- `N(N(P))`. -/
def NNP (G : SimpleGraph V) : Finset V :=
  univ.filter fun w => ∃ u, (∃ p ∈ pend G, G.Adj p u) ∧ G.Adj u w

/-- The vertices lying in the maximum number of copies of `K_4`. -/
def M4 (G : SimpleGraph V) : Finset V := univ.filter fun v => numK4 G v = univ.sup (numK4 G)

/-- The statement of Conjecture 393d. -/
def Conjecture393d : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ matchingNumber (G.induce ((NNP G)ᶜ : Set V)) +
      (G.induce ((maxDegSet G)ᶜ : Set V)).indepNum + #(M4 G)

/-! ### The counterexample -/

def E : List (Fin 12 × Fin 12) :=
  [(0, 2), (0, 3), (0, 6), (0, 7), (0, 9), (1, 2), (1, 3), (1, 6), (1, 7), (1, 10), (1, 11),
    (2, 3), (2, 6), (2, 7), (2, 10), (3, 8), (3, 10), (4, 6), (5, 9), (6, 7), (7, 8), (7, 10),
    (8, 9), (8, 11), (9, 10), (10, 11)]

def adjB (a b : Fin 12) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 12} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 12) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

/-- A neighbour closer to `2`, and the distance from `2`. -/
def par : Fin 12 → Fin 12 := ![2, 2, 2, 2, 6, 9, 2, 2, 3, 0, 2, 1]
def dist2 : Fin 12 → ℕ := ![1, 1, 0, 1, 2, 3, 1, 1, 2, 2, 1, 2]

lemma G_connected : G.Connected := by
  refine WOWII267.connected_of_parent 2 dist2 par fun v hv => ?_
  rw [G_adj]
  revert v
  decide

lemma G_pend : pend G = {4, 5} := by
  ext v
  simp only [pend, mem_filter, mem_univ, true_and, G_degree]
  revert v
  decide

lemma G_NNP : NNP G = {0, 1, 2, 4, 5, 7, 8, 10} := by
  ext w
  simp only [NNP, mem_filter, mem_univ, true_and, G_pend, G_adj]
  constructor
  · rintro ⟨u, ⟨p, hp, hpu⟩, huw⟩
    simp only [mem_insert, mem_singleton] at hp
    revert hpu huw
    rcases hp with rfl | rfl
    · revert u w; decide
    · revert u w; decide
  · intro hw
    have key : ∀ w ∈ ({0, 1, 2, 4, 5, 7, 8, 10} : Finset (Fin 12)), ∃ u,
        (∃ p ∈ ({4, 5} : Finset (Fin 12)), adjB p u = true) ∧ adjB u w = true := by decide
    exact key w hw

lemma G_matching (inst : Fintype ((NNP G)ᶜ : Set (Fin 12))) :
    @matchingNumber _ inst (G.induce ((NNP G)ᶜ : Set (Fin 12))) = 0 := by
  obtain ⟨M, hM, hcard⟩ := exists_max_matching (G.induce ((NNP G)ᶜ : Set (Fin 12)))
  rw [← hcard, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  have heG := hM.1 he
  rw [mem_edgeFinset] at heG
  induction e using Sym2.ind with
  | h a b =>
    have hab : G.Adj a.1 b.1 := heG
    have split : ∀ x : Fin 12, x ∈ ({0, 1, 2, 4, 5, 7, 8, 10} : Finset (Fin 12)) ∨
        x ∈ ({3, 6, 9, 11} : Finset (Fin 12)) := by decide
    have hout : ∀ x : ((NNP G)ᶜ : Set (Fin 12)), x.1 ∈ ({3, 6, 9, 11} : Finset (Fin 12)) := by
      rintro ⟨y, hy⟩
      have hy' : y ∉ NNP G := hy
      rw [G_NNP] at hy'
      exact (split y).resolve_left hy'
    have key : ∀ x ∈ ({3, 6, 9, 11} : Finset (Fin 12)), ∀ y ∈ ({3, 6, 9, 11} : Finset (Fin 12)),
        adjB x y = false := by decide
    rw [G_adj, key a.1 (hout a) b.1 (hout b)] at hab
    exact Bool.false_ne_true hab

lemma G_maxDegree : G.maxDegree = 6 := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rw [G_degree]
    revert v
    decide
  · have : G.degree 2 = 6 := by rw [G_degree]; decide
    rw [← this]
    exact G.degree_le_maxDegree 2

lemma G_maxDegSet : maxDegSet G = {1, 2, 7, 10} := by
  ext v
  simp only [maxDegSet, mem_filter, mem_univ, true_and, G_maxDegree, G_degree]
  revert v
  decide

/-- The edge of the cover containing a vertex outside `M`. -/
def pairIdx (v : Fin 12) : Fin 4 := ![0, 0, 0, 0, 1, 2, 1, 0, 3, 2, 0, 3] v

lemma G_alpha : (G.induce ((maxDegSet G)ᶜ : Set (Fin 12))).indepNum ≤ 4 := by
  obtain ⟨s, hs⟩ := (G.induce ((maxDegSet G)ᶜ : Set (Fin 12))).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  have split : ∀ x : Fin 12, x ∈ ({1, 2, 7, 10} : Finset (Fin 12)) ∨
      x ∈ ({0, 3, 4, 5, 6, 8, 9, 11} : Finset (Fin 12)) := by decide
  have hout : ∀ x : ((maxDegSet G)ᶜ : Set (Fin 12)),
      x.1 ∈ ({0, 3, 4, 5, 6, 8, 9, 11} : Finset (Fin 12)) := by
    rintro ⟨y, hy⟩
    have hy' : y ∉ maxDegSet G := hy
    rw [G_maxDegSet] at hy'
    exact (split y).resolve_left hy'
  have key : ∀ a ∈ ({0, 3, 4, 5, 6, 8, 9, 11} : Finset (Fin 12)),
      ∀ b ∈ ({0, 3, 4, 5, 6, 8, 9, 11} : Finset (Fin 12)),
      a = b ∨ pairIdx a ≠ pairIdx b ∨ adjB a b = true := by decide
  have hinj : Set.InjOn (fun x : ((maxDegSet G)ᶜ : Set (Fin 12)) => pairIdx x.1) s := by
    intro x hx y hy hxy
    rcases key x.1 (hout x) y.1 (hout y) with h | h | h
    · exact Subtype.ext h
    · exact absurd hxy h
    · by_contra hne
      exact hs.isIndepSet hx hy hne (show G.Adj x.1 y.1 from G_adj.mpr h)
  have := card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj
  simpa using this

/-- `numK4` computed from the Boolean adjacency. -/
def numK4B (v : Fin 12) : ℕ :=
  #((univ.filter fun w => adjB v w = true).powersetCard 3 |>.filter fun s =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → adjB a b = true)

lemma numK4_eq (v : Fin 12) : numK4 G v = numK4B v := by
  have hN : G.neighborFinset v = univ.filter fun w => adjB v w = true := by
    ext w
    simp [G_adj]
  rw [numK4, numK4B, hN]
  congr 1
  ext s
  simp only [mem_filter, G_adj]

lemma G_M4 : #(M4 G) = 1 := by
  rw [M4, show numK4 G = numK4B from funext numK4_eq]
  decide

/-- No three vertices together with the pendants `4, 5` form a 2-dominating set. -/
def badB (a b c : Fin 12) : Bool :=
  (List.finRange 12).all fun v =>
    v == 4 || v == 5 || v == a || v == b || v == c ||
      Nat.ble 2 (cond (adjB v 4) 1 0 + cond (adjB v 5) 1 0 + cond (adjB v a) 1 0 +
        cond (adjB v b) 1 0 + cond (adjB v c) 1 0)

lemma badB_false : ∀ a b c : Fin 12, badB a b c = false := by decide

lemma cond_eq (b : Bool) : cond b 1 0 = if b = true then 1 else 0 := by cases b <;> rfl

lemma G_twoDomNum : 6 ≤ twoDomNum G := by
  have hne : {k | ∃ S, IsTwoDom G S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  rw [twoDomNum, ← hcard]
  -- the pendants lie in `S`
  have hpend : ∀ p q : Fin 12, (∀ w, adjB p w = true → w = q) → p ∈ S := by
    intro p q hq
    by_contra hp
    have h := hS p hp
    have hsub : S.filter (G.Adj p) ⊆ {q} := fun w hw =>
      mem_singleton.mpr (hq w (G_adj.mp (mem_filter.mp hw).2))
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  have h4 := hpend 4 6 (by decide)
  have h5 := hpend 5 9 (by decide)
  by_contra hlt
  push Not at hlt
  set T := (S.erase 4).erase 5
  have hT : #T ≤ 3 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨by decide, h5⟩), card_erase_of_mem h4]
    omega
  -- write `T` as `{a, b, c}` with repetitions (`T` may be empty, then use `4`)
  obtain ⟨a, b, c, hTsub⟩ : ∃ a b c : Fin 12, T ⊆ {a, b, c} := by
    interval_cases hk : #T
    · exact ⟨4, 4, 4, by rw [card_eq_zero.mp hk]; exact empty_subset _⟩
    · obtain ⟨a, ha⟩ := card_eq_one.mp hk
      exact ⟨a, a, a, by rw [ha]; intro x hx; simp_all⟩
    · obtain ⟨a, b, -, hab⟩ := card_eq_two.mp hk
      exact ⟨a, b, b, by rw [hab]; intro x hx; simp_all⟩
    · obtain ⟨a, b, c, -, -, -, habc⟩ := card_eq_three.mp hk
      exact ⟨a, b, c, by rw [habc]⟩
  have hSsub : S ⊆ {4, 5, a, b, c} := by
    intro x hx
    by_cases h4x : x = 4
    · simp [h4x]
    by_cases h5x : x = 5
    · simp [h5x]
    have : x ∈ T := mem_erase.mpr ⟨h5x, mem_erase.mpr ⟨h4x, hx⟩⟩
    have := hTsub this
    simp only [mem_insert, mem_singleton] at this ⊢
    tauto
  have hdom : IsTwoDom G {4, 5, a, b, c} := fun v hv =>
    (hS v fun h => hv (hSsub h)).trans (card_le_card (filter_subset_filter _ hSsub))
  have htrue : badB a b c = true := by
    rw [badB, List.all_eq_true]
    intro v _
    by_cases hvS : v ∈ ({4, 5, a, b, c} : Finset (Fin 12))
    · simp only [mem_insert, mem_singleton] at hvS
      rcases hvS with rfl | rfl | rfl | rfl | rfl <;> simp
    · have h2 := hdom v hvS
      have e1 := WOWII402.card_filter_insert_le (G.Adj v) 4 {5, a, b, c}
      have e2 := WOWII402.card_filter_insert_le (G.Adj v) 5 {a, b, c}
      have e3 := WOWII402.card_filter_insert_le (G.Adj v) a {b, c}
      have e4 := WOWII402.card_filter_insert_le (G.Adj v) b {c}
      have e5 : #(({c} : Finset (Fin 12)).filter (G.Adj v)) ≤ if G.Adj v c then 1 else 0 := by
        rw [filter_singleton]
        split_ifs <;> simp
      simp only [G_adj] at e1 e2 e3 e4 e5 h2
      rw [cond_eq, cond_eq, cond_eq, cond_eq, cond_eq]
      simp only [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq]
      right
      omega
  rw [badB_false a b c] at htrue
  exact Bool.false_ne_true htrue

/-- **WOWII Conjecture 393d is false.** -/
theorem not_conjecture393d : ¬ Conjecture393d := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [G_matching _, G_M4] at h1
  have := G_alpha
  have := G_twoDomNum
  omega

end WOWII393d
