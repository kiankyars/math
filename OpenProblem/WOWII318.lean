import OpenProblem.WOWII320

/-!
# Written on the Wall II, Conjecture 318

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 318.** Let `G` be a simple connected graph with `n > 1`. If
> `maximum dist_even(v) ≥ |E(Ḡ)|`, then `G` is well totally dominated.

We prove the conjecture (`conjecture318`).

* `dist_even(v) ≤ n - deg(v) = 1 + deg_Ḡ(v)`, since the neighbours of `v` are at odd distance.
  So for a vertex `x` maximising `dist_even`, all non-adjacent pairs except at most one contain
  `x`.
* A total dominating set `S` contains a neighbour `z` of `x`. If `z` is adjacent to every other
  vertex, then `z` and any of its neighbours in `S` form a total dominating set. Otherwise `z` has
  a single non-neighbour `b`, and `z` together with a neighbour of `b` in `S` is a total dominating
  set. Hence every minimal total dominating set has exactly two vertices.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII318

open SimpleGraph WOWII372 WOWII326 WOWII320

variable {V : Type*} [Fintype V]

lemma degree_add_degree_compl (G : SimpleGraph V) (v : V) :
    G.degree v + Gᶜ.degree v + 1 = Fintype.card V := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hdisj : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [mem_neighborFinset] at hu hu'
    exact ((compl_adj G v u).mp hu').2 hu
  have hunion : G.neighborFinset v ∪ Gᶜ.neighborFinset v = univ.erase v := by
    ext u
    simp only [mem_union, mem_neighborFinset, compl_adj, mem_erase, mem_univ, and_true]
    constructor
    · rintro (h | h)
      · exact (G.ne_of_adj h).symm
      · exact h.1.symm
    · intro hu
      by_cases h : G.Adj v u
      · exact Or.inl h
      · exact Or.inr ⟨Ne.symm hu, h⟩
  rw [← card_union_of_disjoint hdisj, hunion, card_erase_of_mem (mem_univ v), card_univ]
  have := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- **WOWII Conjecture 318.** If `G` is connected with at least two vertices and
`maximum dist_even(v) ≥ |E(Ḡ)|`, then `G` is well totally dominated. -/
theorem conjecture318 (G : SimpleGraph V) (_hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (h : #Gᶜ.edgeFinset ≤ maxDistEven G) : WellTotallyDominated G := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup univ univ_nonempty (distEven G)
  have h1 := distEven_add_degree G x
  have h2 := degree_add_degree_compl G x
  have hmx : maxDistEven G = distEven G x := hx
  -- all non-adjacent pairs except at most one contain `x`
  set R := Gᶜ.edgeFinset \ Gᶜ.incidenceFinset x
  have hR : #R ≤ 1 := by
    have hsub : Gᶜ.incidenceFinset x ⊆ Gᶜ.edgeFinset := Gᶜ.incidenceFinset_subset x
    have hcard : #R + Gᶜ.degree x = #Gᶜ.edgeFinset := by
      rw [← card_incidenceFinset_eq_degree]
      exact card_sdiff_add_card_eq_card hsub
    omega
  have hRmem : ∀ p q, p ≠ q → ¬ G.Adj p q → p ≠ x → q ≠ x → s(p, q) ∈ R := by
    intro p q hpq hadj hpx hqx
    refine mem_sdiff.mpr ⟨Gᶜ.mem_edgeFinset.mpr ((compl_adj G p q).mpr ⟨hpq, hadj⟩), ?_⟩
    rw [mem_incidenceFinset]
    rintro ⟨-, hxe⟩
    rcases Sym2.mem_iff.mp hxe with h | h
    · exact hpx h.symm
    · exact hqx h.symm
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have key : ∀ S, IsMinTDS G S → #S = 2 := by
    intro S ⟨hS, hmin⟩
    -- a neighbour `z` of `x` lies in `S`
    obtain ⟨z, hzS, hxz⟩ := hS x
    have hzx : z ≠ x := (G.ne_of_adj hxz).symm
    have hpair : ∀ u, u ∈ S → G.Adj z u → (∀ t, ∃ w ∈ ({z, u} : Finset V), G.Adj t w) → #S = 2 := by
      intro u huS hzu hT
      have hsub : ({z, u} : Finset V) ⊆ S := by
        intro t ht
        rcases mem_insert.mp ht with rfl | ht
        · exact hzS
        · rw [mem_singleton.mp ht]; exact huS
      have heq : S = {z, u} := by
        by_contra hne
        exact hmin _ (ssubset_of_subset_of_ne hsub (Ne.symm hne)) hT
      rw [heq, card_pair (G.ne_of_adj hzu)]
    by_cases huniv : ∀ u, u ≠ z → G.Adj z u
    · obtain ⟨u, huS, hzu⟩ := hS z
      refine hpair u huS hzu fun t => ?_
      by_cases htz : t = z
      · exact ⟨u, by simp, htz ▸ hzu⟩
      · exact ⟨z, by simp, (huniv t htz).symm⟩
    · push Not at huniv
      obtain ⟨b, hbz, hzb⟩ := huniv
      have hbx : b ≠ x := fun h => hzb (h ▸ hxz.symm)
      -- `b` is the only non-neighbour of `z`
      have huniq : ∀ b', b' ≠ z → ¬ G.Adj z b' → b' = b := by
        intro b' hb'z hzb'
        by_contra hne
        have hb'x : b' ≠ x := fun h => hzb' (h ▸ hxz.symm)
        have e1 := hRmem z b (Ne.symm hbz) hzb hzx hbx
        have e2 := hRmem z b' (Ne.symm hb'z) hzb' hzx hb'x
        have hne' : s(z, b) ≠ s(z, b') := by
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨-, h⟩ | ⟨h, -⟩
          · exact hne h.symm
          · exact hb'z h.symm
        have hsub2 : ({s(z, b), s(z, b')} : Finset (Sym2 V)) ⊆ R := by
          intro e he
          rcases mem_insert.mp he with rfl | he
          · exact e1
          · rw [mem_singleton.mp he]; exact e2
        have := card_le_card hsub2
        rw [card_pair hne'] at this
        omega
      obtain ⟨s, hsS, hbs⟩ := hS b
      have hzs : G.Adj z s := by
        by_contra hzs
        have hsz : s ≠ z := fun h => hzb (h ▸ hbs.symm)
        exact G.ne_of_adj hbs (huniq s hsz hzs).symm
      refine hpair s hsS hzs fun t => ?_
      by_cases htz : t = z
      · exact ⟨s, by simp, htz ▸ hzs⟩
      by_cases htb : t = b
      · exact ⟨s, by simp, htb ▸ hbs⟩
      · have hzt : G.Adj z t := by
          by_contra hzt
          exact htb (huniq t htz hzt)
        exact ⟨z, by simp, hzt.symm⟩
  intro S T hS hT
  rw [key S hS, key T hT]

end WOWII318
