import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 442 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 442.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ n - CEILING[path(G[H_3])/2]`, where `H_3` is the set of vertices of degree at least 3.

Here `α_2` is the 2-independence number, the largest order of a set inducing maximum degree at
most 1. `path(H)` is the longest induced path of `H`, read either as its number of vertices
(`pathOrder`) or as its number of edges.

The fan `F_{1,14}` refutes the conjecture under both readings. It consists of the path
`0 - 1 - ⋯ - 13` together with a vertex `14` adjacent to all path vertices.

* `H_3` contains the inner path vertices `1, …, 12`, which induce a path with `12` vertices.
  So the bound is at most `15 - 6 = 9` under either reading.
* The ten vertices `0, 1, 3, 4, 6, 7, 9, 10, 12, 13` induce five disjoint edges, so `α_2 ≥ 10`.

More generally `α_2(F_{1,p}) = ⌈2p/3⌉` exceeds `p + 1 - ⌈(p - 2)/2⌉` for `p ≥ 11`. All
connected graphs with at most 9 vertices satisfy the conjecture.
-/

open Finset SimpleGraph

open scoped Classical SimpleGraph

noncomputable section

namespace WOWII442

open WOWII449

variable {W : Type*} [Fintype W]

/-- The number of vertices of a longest induced path of `H`. -/
def pathOrder (H : SimpleGraph W) : ℕ := sSup {k | pathGraph k ⊴ H}

lemma le_pathOrder {H : SimpleGraph W} {k : ℕ} (h : pathGraph k ⊴ H) : k ≤ pathOrder H := by
  refine le_csSup ⟨Fintype.card W, ?_⟩ h
  rintro j ⟨f⟩
  simpa using Fintype.card_le_of_injective f f.injective

/-- Conjecture 442, counting the vertices of the longest induced path. -/
def Conjecture442 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    twoIndepNum G ≤ Fintype.card V - (pathOrder (G.induce (H3 G : Set V)) + 1) / 2

/-- Conjecture 442, counting the edges of the longest induced path:
`⌈(k - 1)/2⌉ = ⌊k/2⌋`. -/
def Conjecture442Length : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    twoIndepNum G ≤ Fintype.card V - pathOrder (G.induce (H3 G : Set V)) / 2

/-! ### The fan `F_{1,14}` -/

def fanB (a b : Fin 15) : Bool :=
  (a.val + 1 = b.val && b.val ≤ 13) || (b.val + 1 = a.val && a.val ≤ 13) ||
    (a.val = 14 && b.val ≠ 14) || (b.val = 14 && a.val ≠ 14)

/-- The path `0 - ⋯ - 13` with a vertex `14` adjacent to all of it. -/
def fan : SimpleGraph (Fin 15) := SimpleGraph.fromRel fun a b => fanB a b = true

lemma fan_adj {a b : Fin 15} : fan.Adj a b ↔ fanB a b = true := by
  have h : ∀ a b : Fin 15, (a ≠ b ∧ (fanB a b = true ∨ fanB b a = true)) ↔ fanB a b = true := by
    decide
  simpa [fan] using h a b

lemma fan_degree (v : Fin 15) : fan.degree v = #(univ.filter fun w => fanB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [fan_adj]

lemma fan_connected : fan.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨14, fun w => ?_⟩
  by_cases hw : w = 14
  · rw [hw]
  · exact (fan_adj.mpr (by revert w; decide)).reachable

lemma fan_twoIndepNum : 10 ≤ twoIndepNum fan := by
  let S : Finset (Fin 15) := {0, 1, 3, 4, 6, 7, 9, 10, 12, 13}
  have hS : IsTwoIndep fan S := by
    intro v hv
    rw [filter_congr fun w _ => fan_adj]
    have : ∀ v ∈ S, #(S.filter fun w => fanB v w = true) ≤ 1 := by decide
    exact this v hv
  exact (le_twoIndepNum hS).trans' (by decide)

lemma fan_mem_H3 (i : Fin 12) : (⟨i.val + 1, by omega⟩ : Fin 15) ∈ H3 fan := by
  simp only [H3, mem_filter, mem_univ, true_and, fan_degree]
  revert i
  decide

/-- The inner path `1 - ⋯ - 12` is an induced path of `G[H_3]`. -/
lemma fan_pathOrder : 12 ≤ pathOrder (fan.induce (H3 fan : Set (Fin 15))) := by
  apply le_pathOrder
  let f : Fin 12 → (H3 fan : Set (Fin 15)) := fun i => ⟨⟨i.val + 1, by omega⟩, fan_mem_H3 i⟩
  have hinj : Function.Injective f := by
    intro i j h
    simp only [f, Subtype.mk.injEq, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hadj : ∀ i j : Fin 12, fan.Adj (f i).1 (f j).1 ↔ (pathGraph 12).Adj i j := by
    intro i j
    rw [fan_adj, pathGraph_adj]
    revert i j
    decide
  exact ⟨⟨⟨f, hinj⟩, fun {i j} => by simpa using hadj i j⟩⟩

lemma fan_bound : Fintype.card (Fin 15) - (pathOrder (fan.induce (H3 fan : Set (Fin 15))) + 1) / 2
    < twoIndepNum fan := by
  have h1 := fan_pathOrder
  have h2 := fan_twoIndepNum
  rw [Fintype.card_fin]
  omega

/-- **WOWII Conjecture 442 is false** (path counted by vertices). -/
theorem not_conjecture442 : ¬ Conjecture442 := by
  intro h
  have h1 := h (Fin 15) fan fan_connected (by simp)
  have h2 := fan_bound
  omega

/-- **WOWII Conjecture 442 is false** (path counted by edges). -/
theorem not_conjecture442_length : ¬ Conjecture442Length := by
  intro h
  have h1 := h (Fin 15) fan fan_connected (by simp)
  have h2 := fan_pathOrder
  have h3 := fan_twoIndepNum
  rw [Fintype.card_fin] at h1
  omega

end WOWII442
