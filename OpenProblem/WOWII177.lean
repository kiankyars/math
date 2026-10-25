import OpenProblem.WOWII178
import OpenProblem.WOWII377

/-!
# Written on the Wall II, Conjecture 177 (groundwork)

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 177.** If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ 2α(G) + σ(G)`, where `σ` is the second smallest degree.

This file contains the groundwork for a formal proof: a connected dominating set `D` gives a
spanning tree in which every vertex outside `D` is a leaf, so `L_s(G) ≥ n - |D|`
(`card_compl_le_Ls`). The informal proof is in `wowii/proof177.txt`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII177

open WOWII178

variable {V : Type*} [Fintype V]

/-- `D` is a connected dominating set of `G`. -/
def IsCDS (G : SimpleGraph V) (D : Finset V) : Prop :=
  (∀ v, v ∈ D ∨ ∃ u ∈ D, G.Adj v u) ∧ (G.induce (D : Set V)).Connected

/-- A connected dominating set `D` gives a spanning tree whose leaves include every vertex
outside `D`. -/
lemma card_compl_le_Ls {G : SimpleGraph V} {D : Finset V} (hD : IsCDS G D) :
    #Dᶜ ≤ Ls G := by
  obtain ⟨hdom, hconn⟩ := hD
  have hp : ∀ v, v ∉ D → ∃ u ∈ D, G.Adj v u := fun v hv => (hdom v).resolve_left hv
  choose! p hpD hpG using hp
  -- `G'`: the edges of `G` inside `D`, plus the pendant edges `v - p v`
  set G' : SimpleGraph V :=
    SimpleGraph.fromRel fun a b => (a ∈ D ∧ b ∈ D ∧ G.Adj a b) ∨ (a ∉ D ∧ b = p a) with hG'
  -- `H`: the pendant edges only
  set H : SimpleGraph V := SimpleGraph.fromRel fun a b => a ∉ D ∧ b = p a with hH
  have hHG' : H ≤ G' := by
    intro a b hab
    rw [hH, fromRel_adj] at hab
    rw [hG', fromRel_adj]
    rcases hab with ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl (Or.inr h)⟩
    · exact ⟨hne, Or.inr (Or.inr h)⟩
  have hG'G : G' ≤ G := by
    intro a b hab
    rw [hG', fromRel_adj] at hab
    rcases hab with ⟨-, (⟨-, -, h⟩ | ⟨ha, rfl⟩) | (⟨-, -, h⟩ | ⟨hb, rfl⟩)⟩
    · exact h
    · exact hpG a ha
    · exact h.symm
    · exact (hpG b hb).symm
  have hG'conn : G'.Connected := by
    obtain ⟨⟨d0, hd0⟩⟩ := hconn.nonempty
    have hD' : ∀ v ∈ D, G'.Reachable d0 v := by
      intro v hv
      let φ : G.induce (D : Set V) →g G' :=
        { toFun := fun x => x.1
          map_rel' := fun {x y} hxy => by
            have h : G.Adj x.1 y.1 := by simpa [comap_adj] using hxy
            rw [hG', fromRel_adj]
            exact ⟨G.ne_of_adj h, Or.inl (Or.inl ⟨x.2, y.2, h⟩)⟩ }
      exact (hconn.preconnected ⟨d0, hd0⟩ ⟨v, hv⟩).map φ
    rw [connected_iff_exists_forall_reachable]
    refine ⟨d0, fun v => ?_⟩
    by_cases hv : v ∈ D
    · exact hD' v hv
    · refine (hD' (p v) (hpD v hv)).trans (Adj.reachable ?_)
      rw [hG', fromRel_adj]
      exact ⟨fun h => hv (h ▸ hpD v hv), Or.inr (Or.inr ⟨hv, rfl⟩)⟩
  -- `H` is acyclic: every pendant edge is a bridge
  have hbridge : ∀ x, x ∉ D → H.IsBridge s(x, p x) := by
    intro x hx
    rw [isBridge_iff]
    refine not_reachable_of_closed {x} rfl (fun h => hx (h ▸ hpD x hx)) ?_
    intro a b hab ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [deleteEdges_adj, hH, fromRel_adj] at hab
    obtain ⟨⟨-, h | h⟩, hne⟩ := hab
    · exact absurd (by rw [h.2]; exact Set.mem_singleton _) hne
    · exact absurd (h.2 ▸ hpD b h.1) hx
  have hHac : H.IsAcyclic := by
    rw [isAcyclic_iff_forall_adj_isBridge]
    intro a b hab
    have hab' := hab
    rw [hH, fromRel_adj] at hab'
    rcases hab'.2 with ⟨ha, rfl⟩ | ⟨hb, rfl⟩
    · exact hbridge a ha
    · rw [Sym2.eq_swap]
      exact hbridge b hb
  obtain ⟨T, hHT, hTG', hT⟩ := hG'conn.exists_isTree_le_of_le_of_isAcyclic hHG' hHac
  -- every vertex outside `D` is a leaf of `T`
  have hleaf : ∀ v, v ∉ D → T.degree v = 1 := by
    intro v hv
    rw [← card_neighborFinset_eq_degree, card_eq_one]
    refine ⟨p v, ?_⟩
    ext w
    rw [mem_neighborFinset, mem_singleton]
    constructor
    · intro hvw
      have h := hTG' hvw
      rw [hG', fromRel_adj] at h
      rcases h with ⟨-, (⟨h, -⟩ | ⟨-, rfl⟩) | (⟨-, h, -⟩ | ⟨hw, rfl⟩)⟩
      · exact absurd h hv
      · rfl
      · exact absurd h hv
      · exact absurd (hpD w hw) hv
    · rintro rfl
      apply hHT
      rw [hH, fromRel_adj]
      exact ⟨fun h => hv (h ▸ hpD v hv), Or.inl ⟨hv, rfl⟩⟩
  calc #Dᶜ ≤ numLeaves T := by
        unfold numLeaves
        exact card_le_card fun v hv => by
          rw [mem_filter]
          exact ⟨mem_univ v, hleaf v (mem_compl.mp hv)⟩
    _ ≤ Ls G := le_Ls (hTG'.trans hG'G) hT

/-! ### The second smallest degree -/

/-- `σ(G)`: the second smallest entry of the degree sequence. -/
def sigma (G : SimpleGraph V) : ℕ := (WOWII377.degSeq G).getD 1 0

lemma sigma_le_iff (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (t : ℕ) :
    sigma G ≤ t ↔ 1 < #(univ.filter fun v => G.degree v ≤ t) := by
  rw [sigma, WOWII377.getD_le_iff (l := WOWII377.degSeq G) (Multiset.pairwise_sort _ _)
    (by rw [WOWII377.length_degSeq]; omega), WOWII377.countP_degSeq]

/-- If two distinct vertices have degree at most `t`, then `σ(G) ≤ t`. -/
lemma sigma_le_of_two {G : SimpleGraph V} (hn : 2 ≤ Fintype.card V) {x y : V} (hxy : x ≠ y)
    {t : ℕ} (hx : G.degree x ≤ t) (hy : G.degree y ≤ t) : sigma G ≤ t := by
  rw [sigma_le_iff G hn]
  calc 1 < #({x, y} : Finset V) := by rw [card_pair hxy]; omega
    _ ≤ _ := card_le_card fun v hv => by
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_filter.mpr ⟨mem_univ _, hx⟩
        · rw [mem_singleton.mp hv]; exact mem_filter.mpr ⟨mem_univ _, hy⟩

/-! ### The statement and its reduction to a connected domination bound -/

/-- The statement of Conjecture 177. -/
def Conjecture177 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 ≤ Fintype.card V →
    2 * G.indepNum + sigma G ≤ Ls G + b G

/-- The core bound: for a maximum independent set `S` with at least two vertices, some connected
dominating set `D` satisfies `|D| + σ(G) ≤ |V - S| + α(G[V - S])`. -/
def CoreBound : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 ≤ Fintype.card V →
    ∀ S : Finset V, G.IsNIndepSet G.indepNum S → 2 ≤ #S →
      ∃ D, IsCDS G D ∧ #D + sigma G ≤ #Sᶜ + (G.induce (Sᶜ : Set V)).indepNum

lemma le_b {G : SimpleGraph V} {s : Finset V} (hs : (G.induce (s : Set V)).IsBipartite) :
    #s ≤ b G := by
  apply le_csSup
  · exact ⟨Fintype.card V, by rintro k ⟨s', -, rfl⟩; exact card_le_univ s'⟩
  · exact ⟨s, hs, rfl⟩

/-- A maximum independent set `S` together with an independent set of `G - S` induces a
bipartite subgraph, so `b ≥ α + α(G - S)`. -/
lemma add_le_b {G : SimpleGraph V} {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    #S + (G.induce (Sᶜ : Set V)).indepNum ≤ b G := by
  obtain ⟨J', hJ'⟩ := (G.induce (Sᶜ : Set V)).exists_isNIndepSet_indepNum
  set J : Finset V := J'.map (Function.Embedding.subtype _)
  have hJS : Disjoint S J := by
    rw [Finset.disjoint_left]
    intro v hvS hvJ
    obtain ⟨w, -, rfl⟩ := mem_map.mp hvJ
    exact w.2 (by simpa using hvS)
  have hJind : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    have hne : x' ≠ y' := fun h => G.ne_of_adj hxy (by rw [h])
    exact hJ'.isIndepSet (mem_coe.mpr hx') (mem_coe.mpr hy') hne (by simpa [comap_adj] using hxy)
  have hbip : (G.induce ((S ∪ J : Finset V) : Set V)).IsBipartite := by
    refine ⟨Coloring.mk (fun v => if v.1 ∈ S then 0 else 1) fun {v w} hvw => ?_⟩
    have hadj : G.Adj v.1 w.1 := by simpa [comap_adj] using hvw
    have hv := mem_coe.mp v.2
    have hw := mem_coe.mp w.2
    rw [mem_union] at hv hw
    by_cases hvS : v.1 ∈ S <;> by_cases hwS : w.1 ∈ S <;> simp only [hvS, hwS, ite_true,
      ite_false, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, not_true_eq_false]
    · exact hS (mem_coe.mpr hvS) (mem_coe.mpr hwS) (G.ne_of_adj hadj) hadj
    · exact hJind _ (hv.resolve_left hvS) _ (hw.resolve_left hwS) hadj
  have := le_b hbip
  rw [card_union_of_disjoint hJS, card_map, hJ'.card_eq] at this
  exact this

/-- **The reduction**: the core bound implies Conjecture 177. -/
theorem conjecture177_of_coreBound (h : CoreBound) : Conjecture177 := by
  intro V _ G hG hn
  by_cases hα : G.indepNum ≤ 1
  · -- `G` is complete
    have hcomplete : ∀ x y : V, x ≠ y → G.Adj x y := by
      intro x y hxy
      by_contra hnadj
      have hind : G.IsIndepSet (({x, y} : Finset V) : Set V) := by
        intro a ha c hc hac
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
        rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
        · exact absurd rfl hac
        · exact hnadj
        · exact fun h => hnadj h.symm
        · exact absurd rfl hac
      have := hind.card_le_indepNum
      rw [card_pair hxy] at this
      omega
    obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    -- `L_s ≥ n - 1` from the connected dominating set `{x}`
    have hD : IsCDS G {x} := by
      refine ⟨fun v => ?_, ?_⟩
      · by_cases hv : v = x
        · exact Or.inl (mem_singleton.mpr hv)
        · exact Or.inr ⟨x, mem_singleton_self x, hcomplete v x hv⟩
      · have : Subsingleton ((({x} : Finset V) : Set V)) := by
          rw [coe_singleton]; infer_instance
        have : Nonempty ((({x} : Finset V) : Set V)) := ⟨⟨x, by simp⟩⟩
        exact (connected_iff_exists_forall_reachable _).mpr
          ⟨⟨x, by simp⟩, fun w => by rw [Subsingleton.elim w ⟨x, by simp⟩]⟩
    have hLs := card_compl_le_Ls hD
    rw [card_compl, card_singleton] at hLs
    -- `b ≥ 2` from the edge `xy`
    have hb : 2 ≤ b G := by
      have hbip : (G.induce ((({x, y} : Finset V)) : Set V)).IsBipartite := by
        refine ⟨Coloring.mk (fun v => if v.1 = x then 0 else 1) fun {v w} hvw => ?_⟩
        have hadj : G.Adj v.1 w.1 := by simpa [comap_adj] using hvw
        have hv := mem_coe.mp v.2
        have hw := mem_coe.mp w.2
        simp only [mem_insert, mem_singleton] at hv hw
        rcases hv with hv | hv <;> rcases hw with hw | hw <;>
          simp only [hv, hw, ite_true, ite_false, ne_eq, zero_ne_one, one_ne_zero,
            not_false_eq_true, Ne.symm hxy]
        · exact fun _ => G.ne_of_adj hadj (by rw [hv, hw])
        · exact fun _ => G.ne_of_adj hadj (by rw [hv, hw])
      have := le_b hbip
      rwa [card_pair hxy] at this
    have hσ : sigma G ≤ Fintype.card V - 1 :=
      sigma_le_of_two hn hxy (G.degree_lt_card_verts x |> Nat.le_sub_one_of_lt)
        (G.degree_lt_card_verts y |> Nat.le_sub_one_of_lt)
    omega
  · -- `α ≥ 2`: use a maximum independent set
    obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    have hS2 : 2 ≤ #S := by rw [hS.card_eq]; omega
    obtain ⟨D, hD, hDb⟩ := h V G hG hn S hS hS2
    have hLs := card_compl_le_Ls hD
    have hb := add_le_b hS.isIndepSet
    have hcS := card_add_card_compl S
    have hcD := card_add_card_compl D
    rw [hS.card_eq] at hb hcS hS2
    omega

end WOWII177
