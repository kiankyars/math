import Mathlib

/-!
# Written on the Wall II, Conjecture 382b is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 382b.** Let `G` be a connected graph on `n > 2` vertices. Then
> `γ_2 ≤ -1 + α*(δ + |A_1|)`, where `δ` is the minimum degree and `A_1` is the set of vertices
> that are adjacent to exactly one non-minimum degree vertex.

Here `γ_2` is the 2-domination number: the minimum size of a set `S` such that every vertex
outside `S` has at least two neighbours in `S`.

The triangle `K_3` is a counterexample. It has `γ_2 = 2`, `α = 1`, `δ = 2` and `A_1 = ∅` (all
vertices have the minimum degree), so the right-hand side is `1`.

The WOWII page notes that the conjecture follows from `γ_2 ≤ 2α` unless `δ = 2` and
`A_1 = ∅`, or `δ = 1` and `|A_1| = 1`. In those cases it amounts to `γ_2 ≤ 2α - 1`, which `K_3`
violates. Among connected graphs with at most 9 vertices, `K_3` is the only counterexample.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII382b

open SimpleGraph

variable {V : Type*} [Fintype V]

/-- `S` is 2-dominating: every vertex outside `S` has at least two neighbours in `S`. -/
def IsTwoDom (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∉ S, 2 ≤ #(S.filter (G.Adj v))

/-- The 2-domination number `γ_2(G)`. -/
def twoDomNum (G : SimpleGraph V) : ℕ := sInf {k | ∃ S, IsTwoDom G S ∧ #S = k}

/-- The vertices adjacent to exactly one vertex of non-minimum degree. -/
def A1 (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => #(univ.filter fun w => G.Adj v w ∧ G.degree w ≠ G.minDegree) = 1

/-- The statement of Conjecture 382b. -/
def Conjecture382b : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    (twoDomNum G : ℤ) ≤ -1 + G.indepNum * (G.minDegree + #(A1 G))

/-! ### The triangle -/

/-- The triangle `K_3`. -/
def K3 : SimpleGraph (Fin 3) where
  Adj a b := a ≠ b
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

lemma K3_adj {a b : Fin 3} : K3.Adj a b ↔ a ≠ b := Iff.rfl

lemma K3_connected : K3.Connected := by
  have : K3 = ⊤ := by ext a b; simp [K3_adj]
  rw [this]
  exact connected_top

lemma K3_degree (w : Fin 3) : K3.degree w = 2 := by
  rw [← card_neighborFinset_eq_degree]
  have : K3.neighborFinset w = univ.erase w := by
    ext x
    simp [K3_adj, eq_comm]
  rw [this, card_erase_of_mem (mem_univ w), card_univ, Fintype.card_fin]

lemma K3_minDegree : K3.minDegree = 2 := by
  apply le_antisymm
  · rw [← K3_degree 0]
    exact K3.minDegree_le_degree 0
  · exact le_minDegree_of_forall_le_degree _ _ fun v => (K3_degree v).ge

lemma K3_twoDomNum : 2 ≤ twoDomNum K3 := by
  have hne : {k | ∃ S, IsTwoDom K3 S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  rw [twoDomNum, ← hcard]
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra h
    push Not at h
    have : #(univ : Finset (Fin 3)) ≤ #S := card_le_card fun v _ => h v
    simp at this
    omega
  have := (hS v hv).trans (card_filter_le _ _)
  omega

lemma K3_indepNum : K3.indepNum ≤ 1 := by
  obtain ⟨s, hs⟩ := K3.exists_isNIndepSet_indepNum
  rw [← hs.card_eq, card_le_one]
  intro a ha b hb
  by_contra hab
  exact hs.isIndepSet ha hb hab hab

lemma K3_A1 : A1 K3 = ∅ := by
  ext v
  simp only [A1, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  rw [show (univ.filter fun w => K3.Adj v w ∧ K3.degree w ≠ K3.minDegree) = ∅ by
    ext w
    simp [K3_degree, K3_minDegree]]
  simp

/-- **WOWII Conjecture 382b is false**: the triangle is a counterexample. -/
theorem not_conjecture382b : ¬ Conjecture382b := by
  intro h
  have h1 := h (Fin 3) K3 K3_connected (by simp)
  rw [K3_minDegree, K3_A1, card_empty] at h1
  have h4 : (K3.indepNum : ℤ) ≤ 1 := by exact_mod_cast K3_indepNum
  have h5 : (2 : ℤ) ≤ twoDomNum K3 := by exact_mod_cast K3_twoDomNum
  push_cast at h1
  nlinarith

end WOWII382b
