import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 444 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 444.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ n - FLOOR[dd(K_4(v))/2]`, where `dd(K_4(v))` is the number of distinct values that
> appear in the sequence of the number of `K_4` incident to a vertex.

Here `α_2` is the 2-independence number, the largest order of a set inducing maximum degree at
most 1.

The counterexample `G11` has 11 vertices and 28 edges and was found by simulated annealing. Its
vertices lie in 13, 12, 10, 5, 2, 9, 1, 4, 1, 7 and 0 copies of `K_4`, so ten distinct values
occur and the bound is `11 - 5 = 6`. But the seven vertices `3, 4, 6, 7, 8, 9, 10` induce the
single edge `7 - 9`, so `α_2 ≥ 7`.

The idea is that a few vertices of a dense core (here the clique `0, 1, 2, 5`) can give many
2-independent satellites pairwise distinct `K_4` counts. All connected graphs with at most 9
vertices satisfy the conjecture, and annealing finds no counterexample with 10 vertices.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII444

open WOWII449

variable {V : Type*} [Fintype V]

/-- The number of copies of `K_4` containing `v`: the triangles in `N(v)`. -/
def numK4 (G : SimpleGraph V) (v : V) : ℕ :=
  #((G.neighborFinset v).powersetCard 3 |>.filter fun s => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b)

/-- The number of distinct values of `numK4`. -/
def ddK4 (G : SimpleGraph V) : ℕ := #(univ.image (numK4 G))

/-- The statement of Conjecture 444. -/
def Conjecture444 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    twoIndepNum G ≤ Fintype.card V - ddK4 G / 2

/-! ### The counterexample -/

def E11 : List (Fin 11 × Fin 11) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 3), (1, 4),
    (1, 5), (1, 7), (1, 8), (1, 9), (2, 3), (2, 5), (2, 7), (2, 9), (2, 10), (3, 5), (3, 8),
    (4, 5), (4, 6), (5, 6), (5, 9), (7, 9)]

def adj11 (a b : Fin 11) : Bool := E11.contains (a, b) || E11.contains (b, a)

def G11 : SimpleGraph (Fin 11) := SimpleGraph.fromRel fun a b => adj11 a b = true

lemma G11_adj {a b : Fin 11} : G11.Adj a b ↔ adj11 a b = true := by
  have h : ∀ a b : Fin 11, (a ≠ b ∧ (adj11 a b = true ∨ adj11 b a = true)) ↔
      adj11 a b = true := by decide
  simpa [G11] using h a b

lemma G11_connected : G11.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw]
  by_cases hw' : w = 10
  · rw [hw']
    exact (G11_adj.mpr rfl : G11.Adj 0 2).reachable.trans (G11_adj.mpr rfl : G11.Adj 2 10).reachable
  · exact (G11_adj.mpr (by revert w; decide)).reachable

/-- `numK4` computed from the Boolean adjacency. -/
def numK4B (v : Fin 11) : ℕ :=
  #((univ.filter fun w => adj11 v w = true).powersetCard 3 |>.filter fun s =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → adj11 a b = true)

lemma numK4_eq (v : Fin 11) : numK4 G11 v = numK4B v := by
  have hN : G11.neighborFinset v = univ.filter fun w => adj11 v w = true := by
    ext w
    simp [G11_adj]
  rw [numK4, numK4B, hN]
  congr 1
  ext s
  simp only [mem_filter, G11_adj]

lemma G11_ddK4 : ddK4 G11 = 10 := by
  rw [ddK4, show numK4 G11 = numK4B from funext numK4_eq]
  decide

lemma G11_twoIndepNum : 7 ≤ twoIndepNum G11 := by
  let S : Finset (Fin 11) := {3, 4, 6, 7, 8, 9, 10}
  have hS : IsTwoIndep G11 S := by
    intro v hv
    rw [filter_congr fun w _ => G11_adj]
    have : ∀ v ∈ S, #(S.filter fun w => adj11 v w = true) ≤ 1 := by decide
    exact this v hv
  exact (le_twoIndepNum hS).trans' (by decide)

/-- **WOWII Conjecture 444 is false.** -/
theorem not_conjecture444 : ¬ Conjecture444 := by
  intro h
  have h1 := h (Fin 11) G11 G11_connected (by simp)
  rw [G11_ddK4, Fintype.card_fin] at h1
  have := G11_twoIndepNum
  omega

end WOWII444
