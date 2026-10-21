import OpenProblem.WOWII382b
import OpenProblem.WOWII267

/-!
# Written on the Wall II, Conjecture 402 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 402.** Let `G` be a connected graph on `n > 2` vertices. Then
> `γ_2 ≤ 2[isolates(G[A_δ]) + |{v : |N(v) ∩ A_Δ| = 1}| + γ_t]`, where `A_δ` is the set of
> vertices of minimum degree and `A_Δ` is the set of maximum degree vertices.

Here `γ_2` is the 2-domination number and `γ_t` the total domination number.

The counterexample `G` has 12 vertices and 32 edges and was found by simulated annealing.

* The minimum degree is `3`, attained at the adjacent vertices `2` and `7`, so `G[A_δ]` has no
  isolated vertex.
* The maximum degree is `7`, attained at `0, 1, 9, 10, 11`. Every vertex has zero or at least two
  neighbours among these.
* `{0, 1}` is a total dominating set.

So the bound is at most `2 · 2 = 4`. A finite check shows that no four vertices form a
2-dominating set, so `γ_2 ≥ 5`. The conjecture holds for all connected graphs up to 9 vertices,
and annealing finds counterexamples at 12 vertices but none at 10 or 11.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII402

open WOWII372 WOWII382b

variable {V : Type*} [Fintype V]

/-- The vertices of minimum degree. -/
def Amin (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = G.minDegree

/-- The vertices of maximum degree. -/
def Amax (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = G.maxDegree

/-- The isolated vertices of `G[A_δ]`. -/
def isoMin (G : SimpleGraph V) : ℕ := #((Amin G).filter fun v => ∀ w ∈ Amin G, ¬ G.Adj v w)

/-- The vertices with exactly one neighbour of maximum degree. -/
def oneMax (G : SimpleGraph V) : ℕ := #(univ.filter fun v => #((Amax G).filter (G.Adj v)) = 1)

/-- The statement of Conjecture 402. -/
def Conjecture402 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ 2 * (isoMin G + oneMax G + totalDomNum G)

/-! ### The counterexample -/

def E : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 3), (0, 6), (0, 7), (0, 9), (0, 10), (0, 11), (1, 2), (1, 4), (1, 5), (1, 6),
    (1, 8), (1, 9), (2, 7), (2, 10), (3, 8), (3, 9), (3, 10), (4, 6), (4, 9), (4, 10), (4, 11),
    (5, 6), (5, 8), (5, 9), (6, 11), (7, 11), (8, 10), (8, 11), (9, 10), (9, 11), (10, 11)]

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

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw]
  by_cases h1 : adjB 0 w = true
  · exact (G_adj.mpr h1).reachable
  · have h2 : adjB 1 w = true := by revert w; decide
    exact (G_adj.mpr (rfl : adjB 0 1 = true)).reachable.trans (G_adj.mpr h2).reachable

lemma G_minDegree : G.minDegree = 3 := by
  apply le_antisymm
  · have : G.degree 2 = 3 := by rw [G_degree]; decide
    rw [← this]
    exact G.minDegree_le_degree 2
  · apply le_minDegree_of_forall_le_degree
    intro v
    rw [G_degree]
    revert v
    decide

lemma G_maxDegree : G.maxDegree = 7 := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rw [G_degree]
    revert v
    decide
  · have : G.degree 0 = 7 := by rw [G_degree]; decide
    rw [← this]
    exact G.degree_le_maxDegree 0

lemma G_Amin : Amin G = {2, 7} := by
  ext v
  simp only [Amin, mem_filter, mem_univ, true_and, G_minDegree, G_degree]
  revert v
  decide

lemma G_Amax : Amax G = {0, 1, 9, 10, 11} := by
  ext v
  simp only [Amax, mem_filter, mem_univ, true_and, G_maxDegree, G_degree]
  revert v
  decide

lemma G_isoMin : isoMin G = 0 := by
  rw [isoMin, G_Amin, card_eq_zero, eq_empty_iff_forall_notMem]
  intro v hv
  simp only [mem_filter, mem_insert, mem_singleton] at hv
  obtain ⟨hv, hall⟩ := hv
  rcases hv with rfl | rfl
  · exact hall 7 (Or.inr rfl) (G_adj.mpr rfl)
  · exact hall 2 (Or.inl rfl) (G_adj.mpr rfl)

lemma G_oneMax : oneMax G = 0 := by
  rw [oneMax, G_Amax, card_eq_zero, eq_empty_iff_forall_notMem]
  intro v hv
  simp only [mem_filter, mem_univ, true_and] at hv
  have hc : ((({0, 1, 9, 10, 11} : Finset (Fin 12))).filter (G.Adj v)) =
      ({0, 1, 9, 10, 11} : Finset (Fin 12)).filter fun w => adjB v w = true := by
    ext w
    simp [G_adj]
  rw [hc] at hv
  have key : ∀ v : Fin 12,
      #(({0, 1, 9, 10, 11} : Finset (Fin 12)).filter fun w => adjB v w = true) ≠ 1 := by decide
  exact key v hv

lemma G_totalDomNum : totalDomNum G ≤ 2 := by
  have hS : IsTDS G {0, 1} := by
    have : ∀ v : Fin 12, ∃ u ∈ ({0, 1} : Finset (Fin 12)), adjB v u = true := by decide
    intro v
    obtain ⟨u, hu, h⟩ := this v
    exact ⟨u, hu, G_adj.mpr h⟩
  unfold totalDomNum
  exact (Nat.sInf_le (⟨_, hS, rfl⟩ : #({0, 1} : Finset (Fin 12)) ∈
    {k | ∃ S, IsTDS G S ∧ #S = k})).trans card_le_two

/-- Whether `{a, b, c, d}` is 2-dominating, computed from the Boolean adjacency. -/
def twoDomB (a b c d : Fin 12) : Bool :=
  (List.finRange 12).all fun v =>
    v == a || v == b || v == c || v == d ||
      Nat.ble 2 (cond (adjB v a) 1 0 + cond (adjB v b) 1 0 + cond (adjB v c) 1 0 +
        cond (adjB v d) 1 0)

/-- Four distinct vertices forming a 2-dominating set. -/
def badB (a b c d : Fin 12) : Bool :=
  (a != b) && (a != c) && (a != d) && (b != c) && (b != d) && (c != d) && twoDomB a b c d

lemma badB_false : ∀ a b c d : Fin 12, badB a b c d = false := by decide

lemma cond_eq (b : Bool) : cond b 1 0 = if b = true then 1 else 0 := by cases b <;> rfl

lemma card_filter_insert_le (p : Fin 12 → Prop) [DecidablePred p] (x : Fin 12)
    (s : Finset (Fin 12)) : #((insert x s).filter p) ≤ (if p x then 1 else 0) + #(s.filter p) := by
  rw [Finset.filter_insert (p := p) x s]
  split_ifs
  · exact (card_insert_le x (s.filter p)).trans (by omega)
  · omega

/-- No four vertices form a 2-dominating set. -/
lemma not_twoDom_four (a b c d : Fin 12) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ¬ IsTwoDom G {a, b, c, d} := by
  intro h
  have htrue : twoDomB a b c d = true := by
    rw [twoDomB, List.all_eq_true]
    intro v _
    by_cases hvS : v ∈ ({a, b, c, d} : Finset (Fin 12))
    · simp only [mem_insert, mem_singleton] at hvS
      rcases hvS with rfl | rfl | rfl | rfl <;> simp
    · have h2 := h v hvS
      have e1 := card_filter_insert_le (G.Adj v) a {b, c, d}
      have e2 := card_filter_insert_le (G.Adj v) b {c, d}
      have e3 := card_filter_insert_le (G.Adj v) c {d}
      have e4 : #(({d} : Finset (Fin 12)).filter (G.Adj v)) ≤ if G.Adj v d then 1 else 0 := by
        rw [filter_singleton]
        split_ifs <;> simp
      simp only [G_adj] at e1 e2 e3 e4 h2
      rw [cond_eq, cond_eq, cond_eq, cond_eq]
      simp only [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq]
      right
      omega
  have hne : ∀ x y : Fin 12, x ≠ y → (x != y) = true := fun x y h => bne_iff_ne.mpr h
  have := badB_false a b c d
  rw [badB, htrue, hne a b hab, hne a c hac, hne a d had, hne b c hbc, hne b d hbd,
    hne c d hcd] at this
  exact Bool.false_ne_true this.symm

lemma G_twoDomNum : 5 ≤ twoDomNum G := by
  have hne : {k | ∃ S, IsTwoDom G S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  rw [twoDomNum, ← hcard]
  by_contra hlt
  push Not at hlt
  -- enlarge `S` to exactly four vertices
  obtain ⟨T, hST, hT⟩ := exists_superset_card_eq (s := S) (n := 4) (by omega) (by simp)
  have hTdom : IsTwoDom G T := by
    intro v hv
    exact (hS v fun h => hv (hST h)).trans (card_le_card (filter_subset_filter _ hST))
  obtain ⟨a, T', haT', rfl, hT'⟩ := card_eq_succ.mp hT
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := card_eq_three.mp hT'
  simp only [mem_insert, mem_singleton, not_or] at haT'
  exact not_twoDom_four a b c d haT'.1 haT'.2.1 haT'.2.2 hbc hbd hcd hTdom

/-- **WOWII Conjecture 402 is false.** -/
theorem not_conjecture402 : ¬ Conjecture402 := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [G_isoMin, G_oneMax] at h1
  have := G_totalDomNum
  have := G_twoDomNum
  omega

end WOWII402
