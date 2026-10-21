import OpenProblem.WOWII412f
import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 391 is false as stated

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 391.** If `G` is a connected graph on `n > 2` vertices, then
> `γ_2 ≤ p(G) + 1 + μ(G[T]) + |E(G[A_3])|`, where `T` is the set of vertices of degree two and
> `A_3` is the set of vertices of degree at least three.

Here `γ_2` is the 2-domination number, `p` the path cover number (as tagged in the transcription
and as in the neighbouring conjectures 372, 407 and 418b), and `μ` the matching number.

The conjecture fails for the spider with legs of lengths `1, 1, 2` (`not_conjecture391`): the
centre `4` is adjacent to the leaves `1, 2` and to `0`, which is adjacent to the leaf `3`.

* The three leaves lie in every 2-dominating set, and so does `0` or `4`, so `γ_2 = 4`.
* The paths `3 - 0 - 4 - 1` and `2` cover the vertices, so `p ≤ 2`.
* `T = {0}` and `A_3 = {4}`, so `μ(G[T]) = |E(G[A_3])| = 0`.

So the right-hand side is at most `3`. Reading `p(G)` as the number of pendants instead, the bound
still fails, for example for the 8-vertex graph `G?Bcr_`. A failure on five vertices points to a
transcription problem.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII391

open WOWII382b WOWII372 WOWII412f WOWII449

variable {V : Type*} [Fintype V]

/-- The vertices of degree two. -/
def deg2Set (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = 2

/-- The vertices of degree at least three. -/
def deg3Set (G : SimpleGraph V) : Finset V := univ.filter fun v => 3 ≤ G.degree v

/-- The statement of Conjecture 391. -/
def Conjecture391 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ pathCoverNumber G + 1 + matchIn G (deg2Set G) + edgesIn G (deg3Set G)

/-! ### The counterexample -/

/-- The edges of the spider. -/
def E : List (Fin 5 × Fin 5) := [(0, 3), (0, 4), (1, 4), (2, 4)]

/-- Adjacency in the spider. -/
def adjB (a b : Fin 5) : Bool := E.contains (a, b) || E.contains (b, a)

/-- The spider with legs of lengths `1, 1, 2`. -/
def G : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 5} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 5, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 5) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨4, fun w => ?_⟩
  by_cases hw : w = 4
  · rw [hw]
  by_cases h1 : adjB 4 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 4 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

lemma G_twoDomNum : 4 ≤ twoDomNum G := by
  have key : ∀ S : Finset (Fin 5),
      (∀ v ∉ S, 2 ≤ #(S.filter fun w => adjB v w = true)) → 4 ≤ #S := by decide
  refine le_csInf ⟨5, univ, fun v hv => absurd (mem_univ v) hv, by simp⟩ ?_
  rintro k ⟨S, hS, rfl⟩
  refine key S fun v hv => ?_
  have := hS v hv
  simpa only [G_adj] using this

lemma G_pathCoverNumber : pathCoverNumber G ≤ 2 := by
  have h30 : G.Adj 3 0 := G_adj.mpr (by decide)
  have h04 : G.Adj 0 4 := G_adj.mpr (by decide)
  have h41 : G.Adj 4 1 := G_adj.mpr (by decide)
  let p : G.Walk 3 1 := Walk.cons h30 (Walk.cons h04 (Walk.cons h41 Walk.nil))
  have hp : p.IsPath := by
    simp only [p, Walk.cons_isPath_iff, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, Walk.IsPath.nil]
    decide
  refine Nat.sInf_le ⟨{{3, 0, 4, 1}, {2}}, by decide, ?_, ?_, ?_⟩
  · intro s1 h1 s2 h2 hne
    simp only [mem_insert, mem_singleton] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  · intro v _
    simp only [mem_biUnion, mem_insert, mem_singleton, id]
    have : v ∈ ({3, 0, 4, 1} : Finset (Fin 5)) ∨ v = 2 := by revert v; decide
    rcases this with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, by simp [h]⟩
  · intro s hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl
    · refine ⟨3, 1, p, hp, ?_⟩
      ext x
      simp only [p, Walk.support_cons, Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
        mem_insert, mem_singleton, insert_empty]
    · exact ⟨2, 2, Walk.nil, Walk.IsPath.nil, by simp⟩

lemma G_deg2Set : deg2Set G = {0} := by
  ext v
  simp only [deg2Set, mem_filter, mem_univ, true_and, G_degree, mem_singleton]
  revert v
  decide

lemma G_deg3Set : deg3Set G = {4} := by
  ext v
  simp only [deg3Set, mem_filter, mem_univ, true_and, G_degree, mem_singleton]
  revert v
  decide

lemma matchIn_singleton (H : SimpleGraph V) (a : V) : matchIn H {a} = 0 := by
  refine le_antisymm (csSup_le ⟨0, ∅, ⟨empty_subset _, by simp⟩, by simp, rfl⟩ ?_)
    (Nat.zero_le _)
  rintro k ⟨M, hM, hin, rfl⟩
  rw [Nat.le_zero, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have hu := hin _ he u (Sym2.mem_mk_left u v)
    have hv := hin _ he v (Sym2.mem_mk_right u v)
    rw [mem_singleton] at hu hv
    have := hM.1 he
    rw [mem_edgeFinset, mem_edgeSet, hu, hv] at this
    exact H.irrefl this

lemma edgesIn_singleton (H : SimpleGraph V) (a : V) : edgesIn H {a} = 0 := by
  rw [edgesIn, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_filter] at he
  induction e using Sym2.ind with
  | _ u v =>
    have hu := he.2 u (Sym2.mem_mk_left u v)
    have hv := he.2 v (Sym2.mem_mk_right u v)
    rw [mem_singleton] at hu hv
    have := he.1
    rw [mem_edgeFinset, mem_edgeSet, hu, hv] at this
    exact H.irrefl this

/-- **WOWII Conjecture 391 is false as stated.** -/
theorem not_conjecture391 : ¬ Conjecture391 := by
  intro h
  have h1 := h (Fin 5) G G_connected (by simp)
  rw [G_deg2Set, G_deg3Set, matchIn_singleton, edgesIn_singleton] at h1
  have := G_twoDomNum
  have := G_pathCoverNumber
  omega

end WOWII391
