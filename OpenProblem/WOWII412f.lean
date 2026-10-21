import OpenProblem.WOWII382b
import OpenProblem.WOWII325

/-!
# Written on the Wall II, Conjecture 412f is false as stated

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 412f.** Let `G` be a connected graph on `n > 2` vertices, `P` the set of pendant
> vertices and `H` the union of all maximum critical independent sets of `G`. Then
> `|H| ≥ μ(G[V - N(P)])`, and if `G` is also bipartite, then
> `|H| ≥ c(G[V - N(P)]) + μ(G[V - N(P)])`.

Here `μ` is the matching number and `c` the number of components. Following Zhang and Larson, the
*critical difference* of `G` is the largest value of `|X| - |N(X)|` over all vertex sets `X`
(it is at least `0`, the value for `X = ∅`), and an independent set `I` is *critical* if
`|I| - |N(I)|` equals the critical difference.

The first clause fails for the triangle `K_3` (`not_conjecture412f`). There `P = ∅`, so
`μ(G[V - N(P)]) = μ(K_3) = 1`. The critical difference of `K_3` is `0`, attained by `∅`, while a
single vertex `v` has `|{v}| - |N(v)| = -1`. So `∅` is the only critical independent set, and
`H = ∅`. Graffiti.pc checked its conjectures against a database that contains `K_3`, so the first
clause is probably a transcription problem. The bipartite clause holds for all bipartite graphs
with at most 10 vertices, and remains open.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII412f

open WOWII382b WOWII326 WOWII325

variable {V : Type*} [Fintype V]

/-- The open neighbourhood `N(X)` of a vertex set. -/
def nbhd (G : SimpleGraph V) (X : Finset V) : Finset V := univ.filter fun v => ∃ x ∈ X, G.Adj x v

/-- The difference `|X| - |N(X)|`. -/
def diff (G : SimpleGraph V) (X : Finset V) : ℤ := #X - #(nbhd G X)

/-- The critical difference: the largest `|X| - |N(X)|` over all vertex sets `X`. -/
def critDiff (G : SimpleGraph V) : ℤ := (univ : Finset (Finset V)).sup' univ_nonempty (diff G)

/-- `I` is independent. -/
def IsIndep (G : SimpleGraph V) (I : Finset V) : Prop := ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y

/-- `I` is a critical independent set. -/
def IsCritIndep (G : SimpleGraph V) (I : Finset V) : Prop := IsIndep G I ∧ diff G I = critDiff G

/-- The critical independence number: the largest size of a critical independent set. -/
def critIndepNum (G : SimpleGraph V) : ℕ := sSup {k | ∃ I, IsCritIndep G I ∧ #I = k}

/-- The union `H` of all maximum critical independent sets. -/
def unionMaxCrit (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => ∃ I, IsCritIndep G I ∧ #I = critIndepNum G ∧ v ∈ I

/-- The pendant vertices. -/
def pendants (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = 1

/-- The matching number of `G[W]`: the largest matching using only edges inside `W`. -/
def matchIn (G : SimpleGraph V) (W : Finset V) : ℕ :=
  sSup {k | ∃ M, IsMatching G M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ W) ∧ #M = k}

/-- The statement of Conjecture 412f. -/
def Conjecture412f : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    matchIn G (univ \ nbhd G (pendants G)) ≤ #(unionMaxCrit G) ∧
      (G.Colorable 2 → numComp G (univ \ nbhd G (pendants G)) +
        matchIn G (univ \ nbhd G (pendants G)) ≤ #(unionMaxCrit G))

/-! ### The triangle -/

lemma K3_pendants : pendants K3 = ∅ := by
  ext v
  simp [pendants, K3_degree]

lemma K3_matchIn (W : Finset (Fin 3)) (hW : ∀ v, v ∈ W) : 1 ≤ matchIn K3 W := by
  refine le_csSup ⟨#(K3.edgeFinset), fun k ⟨M, hM, _, hk⟩ => hk ▸ card_le_card hM.1⟩
    ⟨{s(0, 1)}, ⟨fun e he => ?_, fun e he f hf hef => ?_⟩, fun _ _ v _ => hW v, rfl⟩
  · rw [mem_singleton] at he
    subst he
    rw [mem_edgeFinset, mem_edgeSet, K3_adj]
    decide
  · rw [mem_singleton] at he hf
    exact absurd (he.trans hf.symm) hef

/-- An independent set of the triangle has at most one vertex. -/
lemma K3_indep_card {I : Finset (Fin 3)} (hI : IsIndep K3 I) : #I ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  by_contra hab
  exact hI a ha b hb (K3_adj.mpr hab)

lemma K3_diff_singleton (v : Fin 3) : diff K3 {v} = -1 := by
  have : #(nbhd K3 {v}) = 2 := by
    simp only [nbhd, mem_singleton, exists_eq_left, K3_adj]
    revert v
    decide
  simp [diff, this]

/-- The only critical independent set of the triangle is `∅`. -/
lemma K3_critIndep {I : Finset (Fin 3)} (hI : IsCritIndep K3 I) : I = ∅ := by
  have h0 : diff K3 ∅ ≤ critDiff K3 := le_sup' (diff K3) (mem_univ ∅)
  have hd0 : diff K3 ∅ = 0 := by simp [diff, nbhd]
  rcases (card_le_one_iff_subset_singleton.mp (K3_indep_card hI.1)) with ⟨v, hv⟩
  rcases subset_singleton_iff.mp hv with rfl | rfl
  · rfl
  · have := hI.2
    rw [K3_diff_singleton] at this
    omega

lemma K3_unionMaxCrit : unionMaxCrit K3 = ∅ := by
  ext v
  simp only [unionMaxCrit, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  rintro ⟨I, hI, -, hv⟩
  rw [K3_critIndep hI] at hv
  exact notMem_empty v hv

/-- **WOWII Conjecture 412f is false as stated**: its first clause fails for the triangle. -/
theorem not_conjecture412f : ¬ Conjecture412f := by
  intro h
  have h1 := (h (Fin 3) K3 K3_connected (by simp)).1
  have h2 := le_trans (K3_matchIn _ fun v => ?_) h1
  · rw [K3_unionMaxCrit, card_empty] at h2
    omega
  · simp [K3_pendants, nbhd]

end WOWII412f
