import OpenProblem.WOWII178

/-!
# Written on the Wall II, Conjecture 161

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 161.** If `G` is a simple connected graph, then `L_s(G) ≥ maximum of λ(v) of Ḡ`.

Here `L_s` is the maximum number of leaves of a spanning tree, and `λ(v)` computed in the
complement `Ḡ` is the independence number of `Ḡ[N_Ḡ(v)]`. That is the largest clique of `G`
consisting of vertices not adjacent to `v`.

We prove the conjecture (`conjecture161`). Let `K` be a clique of `G` avoiding `N[v]`. Since `G`
is connected and `v ∉ K`, some `x ∈ K` has a neighbour outside `K`, so
`deg x ≥ (|K| - 1) + 1 = |K|`. A spanning tree containing all edges at `x` has at least `deg x`
leaves, hence `L_s(G) ≥ |K|`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII161

open SimpleGraph WOWII178

variable {V : Type*} [Fintype V]

/-- A connected graph on at least two vertices has a spanning tree with at least `deg x` leaves. -/
lemma degree_le_Ls {G : SimpleGraph V} (hG : G.Connected) (hn : 2 ≤ Fintype.card V) (x : V) :
    G.degree x ≤ Ls G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (hG.preconnected.degree_pos_of_nontrivial x)
  obtain ⟨T, hTG, hT, hu, -⟩ := exists_tree_doubleStar hG hxy
  have h1 : G.degree x ≤ T.degree x := by
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    exact card_le_card fun z hz =>
      (T.mem_neighborFinset x z).mpr (hu z ((G.mem_neighborFinset x z).mp hz))
  have h2 := sum_degree_le hT {x}
  rw [sum_singleton, card_singleton] at h2
  have h3 := le_Ls hTG hT
  omega

/-- **WOWII Conjecture 161.** For every connected graph on at least two vertices,
`L_s(G) ≥ max_v λ_Ḡ(v)`. -/
theorem conjecture161 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    maxLocalIndep Gᶜ ≤ Ls G := by
  apply Finset.sup_le
  intro v _
  obtain ⟨I, hIv, hII, hcard⟩ := exists_indep_nbhd Gᶜ v
  rw [← hcard]
  -- `I` is a clique of `G` avoiding `N[v]`
  have hIclique : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → G.Adj x y := by
    intro x hx y hy hxy
    by_contra h
    exact hII x hx y hy ((compl_adj G x y).mpr ⟨hxy, h⟩)
  have hvI : v ∉ I := fun h => ((compl_adj G v v).mp (hIv v h)).1 rfl
  rcases I.eq_empty_or_nonempty with hI | ⟨x0, hx0⟩
  · rw [hI, card_empty]; exact Nat.zero_le _
  -- some vertex of `I` has a neighbour outside `I`
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ I, ∃ y, y ∉ I ∧ G.Adj x y := by
    by_contra hno
    push Not at hno
    have hcl : ∀ a b, G.Adj a b → a ∈ (I : Set V) → b ∈ (I : Set V) := by
      intro a b hab ha
      by_contra hb
      exact hno a ha b hb hab
    exact not_reachable_of_closed (I : Set V) hx0 hvI hcl (hG.preconnected x0 v)
  -- so `deg x ≥ |I|`
  have hdeg : #I ≤ G.degree x := by
    rw [← card_neighborFinset_eq_degree]
    have hsub : insert y (I.erase x) ⊆ G.neighborFinset x := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact (G.mem_neighborFinset x z).mpr hxy
      · have := mem_erase.mp hz
        exact (G.mem_neighborFinset x z).mpr (hIclique x hx z this.2 (Ne.symm this.1))
    have := card_le_card hsub
    rw [card_insert_of_notMem (fun h => hy (mem_of_mem_erase h)), card_erase_of_mem hx] at this
    have := card_pos.mpr ⟨x, hx⟩
    omega
  exact hdeg.trans (degree_le_Ls hG hn x)

end WOWII161
