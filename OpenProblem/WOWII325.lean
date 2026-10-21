import OpenProblem.WOWII323

/-!
# Written on the Wall II, Conjecture 325

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 325.** Let `G` be a simple connected graph with `n > 1`. If
> `min {|N_Ḡ(e)| : e an edge of Ḡ} ≤ 1 + (number of components of ⟨N[S]⟩)`, where `S` is the set of
> vertices of degree two, then `G` is well totally dominated.

Here `N_Ḡ(uw) = N_Ḡ(u) ∪ N_Ḡ(w)` and `⟨N[S]⟩` is the subgraph induced by the closed neighbourhood of
`S`. We prove the conjecture (`conjecture325`). It also holds for complete graphs, where `Ḡ` has no
edges (`conjecture325'`).

Let `uw` be an edge of `Ḡ` attaining the minimum, `X = N(u) ∩ N(w)` and `R = V - X - {u, w}`. Since
`|N_Ḡ(u) ∪ N_Ḡ(w)| = n - |X|`, the hypothesis reads `|R| + 1 ≤ c`, where `c` is the number of
components of `⟨N[S]⟩`. Every component contains a vertex of degree two and its two neighbours, so
it has at least three vertices.

* If some degree-two vertex lies in `X`, its neighbours are `u` and `w`, which therefore lie in one
  component together with `X ∩ N[S]`. The other components lie inside `R`, so `3(c - 1) ≤ |R|`.
  Hence `c = 1` and `R = ∅`, and that vertex has no neighbour in `X`.
* Otherwise `S ⊆ R ∪ {u, w}`. If `u, w ∉ S`, then `c ≤ |S| ≤ |R|`, which is impossible. If `u` (say)
  has degree two, then `|X| ≤ 2`, and `3c ≤ n` again forces `R = ∅`.

So `u` and `w` are adjacent to every other vertex. A minimal total dominating set containing `u` or
`w` is then a pair. One inside `X` either misses a vertex whose only neighbours are `u` and `w`, or
has at most two vertices.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII325

open WOWII372 WOWII326 WOWII323

variable {V : Type*} [Fintype V]

/-! ### Definitions -/

/-- The vertices of degree two. -/
def degTwo (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = 2

/-- The closed neighbourhood `N[S]` of a set. -/
def closedNbhd (G : SimpleGraph V) (S : Finset V) : Finset V :=
  univ.filter fun v => v ∈ S ∨ ∃ s ∈ S, G.Adj v s

/-- The number of connected components of `G[A]`. -/
def numComp (G : SimpleGraph V) (A : Finset V) : ℕ :=
  Fintype.card (G.induce (A : Set V)).ConnectedComponent

/-- The statement of Conjecture 325, for graphs whose complement has an edge. -/
def Conjecture325 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 1 < Fintype.card V →
    (∃ e ∈ Gᶜ.edgeFinset, complNbr G e ≤ 1 + numComp G (closedNbhd G (degTwo G))) →
      WellTotallyDominated G

/-- Conjecture 325, also covering complete graphs (where the minimum is over an empty set). -/
def Conjecture325' : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 1 < Fintype.card V →
    (Gᶜ.edgeFinset = ∅ ∨
      ∃ e ∈ Gᶜ.edgeFinset, complNbr G e ≤ 1 + numComp G (closedNbhd G (degTwo G))) →
      WellTotallyDominated G

/-! ### Components of `⟨N[S]⟩` -/

section Components

variable (G : SimpleGraph V)

local notation "NS" => closedNbhd G (degTwo G)

lemma mem_NS_of_deg {s : V} (hs : G.degree s = 2) : s ∈ NS := by
  simp [closedNbhd, degTwo, hs]

lemma mem_NS_of_adj {v s : V} (hs : G.degree s = 2) (h : G.Adj v s) : v ∈ NS := by
  simp only [closedNbhd, mem_filter, mem_univ, true_and]
  exact Or.inr ⟨s, by simp [degTwo, hs], h⟩

/-- Every component of `⟨N[S]⟩` contains a vertex of degree two. -/
lemma exists_deg_two (C : (G.induce (NS : Set V)).ConnectedComponent) :
    ∃ (s : V) (hs : s ∈ (NS : Set V)), G.degree s = 2 ∧
      (G.induce (NS : Set V)).connectedComponentMk ⟨s, hs⟩ = C := by
  induction C using ConnectedComponent.ind with
  | h v =>
    have hv : v.1 ∈ NS := v.2
    simp only [closedNbhd, mem_filter, mem_univ, true_and, degTwo] at hv
    rcases hv with hv | ⟨s, hs, hvs⟩
    · exact ⟨v.1, v.2, hv, rfl⟩
    · have hsNS : s ∈ (NS : Set V) := mem_NS_of_deg G hs
      refine ⟨s, hsNS, hs, ?_⟩
      exact ConnectedComponent.eq.mpr (Adj.reachable (G := G.induce (NS : Set V))
        (show G.Adj s v.1 from hvs.symm))

/-- Every component of `⟨N[S]⟩` has at least three vertices. -/
lemma three_le_fiber (C : (G.induce (NS : Set V)).ConnectedComponent) :
    3 ≤ #(univ.filter fun v => (G.induce (NS : Set V)).connectedComponentMk v = C) := by
  obtain ⟨s, hs, hdeg, hC⟩ := exists_deg_two G C
  obtain ⟨a, b, hab, hnb⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G s).trans hdeg)
  have ha : G.Adj s a := (mem_neighborFinset G s a).mp (hnb ▸ by simp)
  have hb : G.Adj s b := (mem_neighborFinset G s b).mp (hnb ▸ by simp)
  have haNS : a ∈ (NS : Set V) := mem_NS_of_adj G hdeg ha.symm
  have hbNS : b ∈ (NS : Set V) := mem_NS_of_adj G hdeg hb.symm
  have hCa : (G.induce (NS : Set V)).connectedComponentMk ⟨a, haNS⟩ = C := by
    rw [← hC]
    exact ConnectedComponent.eq.mpr (Adj.reachable (G := G.induce (NS : Set V))
      (show G.Adj a s from ha.symm))
  have hCb : (G.induce (NS : Set V)).connectedComponentMk ⟨b, hbNS⟩ = C := by
    rw [← hC]
    exact ConnectedComponent.eq.mpr (Adj.reachable (G := G.induce (NS : Set V))
      (show G.Adj b s from hb.symm))
  have hsub : ({⟨s, hs⟩, ⟨a, haNS⟩, ⟨b, hbNS⟩} : Finset (NS : Set V)) ⊆
      univ.filter fun v => (G.induce (NS : Set V)).connectedComponentMk v = C := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    simp only [mem_filter, mem_univ, true_and]
    rcases hv with rfl | rfl | rfl
    · exact hC
    · exact hCa
    · exact hCb
  refine le_trans ?_ (card_le_card hsub)
  rw [card_insert_of_notMem, card_pair]
  · intro h
    exact hab (congrArg Subtype.val h)
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => G.ne_of_adj ha (congrArg Subtype.val h),
      fun h => G.ne_of_adj hb (congrArg Subtype.val h)⟩

lemma card_NS : Fintype.card (NS : Set V) = #NS := by
  simp

/-- `3c ≤ |N[S]|`. -/
lemma three_mul_numComp_le : 3 * numComp G NS ≤ #NS := by
  rw [← card_NS, ← card_univ, card_eq_sum_card_fiberwise
    (f := (G.induce (NS : Set V)).connectedComponentMk) (t := univ) (fun _ _ => mem_univ _)]
  rw [numComp, ← card_univ, mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum fun C _ => three_le_fiber G C

/-- `c ≤ |S|`. -/
lemma numComp_le_card : numComp G NS ≤ #(degTwo G) := by
  let f : {s : (NS : Set V) // s.1 ∈ degTwo G} → (G.induce (NS : Set V)).ConnectedComponent :=
    fun s => (G.induce (NS : Set V)).connectedComponentMk s.1
  have hf : Function.Surjective f := by
    intro C
    obtain ⟨s, hs, hdeg, hC⟩ := exists_deg_two G C
    exact ⟨⟨⟨s, hs⟩, by simp [degTwo, hdeg]⟩, hC⟩
  refine (Fintype.card_le_of_surjective f hf).trans ?_
  rw [Fintype.card_subtype]
  refine card_le_card_of_injOn (fun s => s.1) (fun s hs => ?_) (fun s _ t _ h => Subtype.ext h)
  simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hs
  exact hs

/-- The components other than a given one have at least `3(c - 1)` vertices. -/
lemma three_mul_le_off (C0 : (G.induce (NS : Set V)).ConnectedComponent) :
    3 * (numComp G NS - 1) ≤
      #(univ.filter fun v => (G.induce (NS : Set V)).connectedComponentMk v ≠ C0) := by
  rw [card_eq_sum_card_fiberwise (f := (G.induce (NS : Set V)).connectedComponentMk)
    (t := univ.erase C0) (fun v hv => by simpa using hv)]
  have hcard : #(univ.erase C0) = numComp G NS - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, numComp]
  rw [← hcard, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun C hC => ?_
  have hCne : C ≠ C0 := (mem_erase.mp hC).1
  refine (three_le_fiber G C).trans (card_le_card fun v hv => ?_)
  simp only [mem_filter, mem_univ, true_and] at hv ⊢
  exact ⟨hv ▸ hCne, hv⟩

end Components

/-! ### The conjecture -/

/-- If two non-adjacent vertices are adjacent to everything else, and either some other vertex is
adjacent only to them or `n ≤ 4`, then every minimal total dominating set has two vertices. -/
lemma two_of_struct (G : SimpleGraph V) {u w : V} (huw : u ≠ w) (hnadj : ¬ G.Adj u w)
    (hR : ∀ z, z ≠ u → z ≠ w → G.Adj u z ∧ G.Adj w z)
    (hQ : (∃ x0, x0 ≠ u ∧ x0 ≠ w ∧ ∀ y, G.Adj x0 y → y = u ∨ y = w) ∨ Fintype.card V ≤ 4) :
    ∀ S, IsMinTDS G S → #S = 2 := by
  intro S hS
  by_cases hu : u ∈ S
  · obtain ⟨x, hxS, hux⟩ := hS.1 u
    have hxu : x ≠ u := (G.ne_of_adj hux).symm
    have hxw : x ≠ w := fun h => hnadj (h ▸ hux)
    refine card_eq_two hS hu hxS hxu.symm fun z => ?_
    by_cases hzu : z = u
    · exact ⟨x, by simp, hzu ▸ hux⟩
    by_cases hzw : z = w
    · exact ⟨x, by simp, hzw ▸ (hR x hxu hxw).2⟩
    · exact ⟨u, by simp, (hR z hzu hzw).1.symm⟩
  by_cases hw : w ∈ S
  · obtain ⟨x, hxS, hwx⟩ := hS.1 w
    have hxw : x ≠ w := (G.ne_of_adj hwx).symm
    have hxu : x ≠ u := fun h => hnadj (h ▸ hwx).symm
    refine card_eq_two hS hw hxS hxw.symm fun z => ?_
    by_cases hzw : z = w
    · exact ⟨x, by simp, hzw ▸ hwx⟩
    by_cases hzu : z = u
    · exact ⟨x, by simp, hzu ▸ (hR x hxu hxw).1⟩
    · exact ⟨w, by simp, (hR z hzu hzw).2.symm⟩
  rcases hQ with ⟨x0, -, -, hx0⟩ | hn4
  · obtain ⟨y, hyS, hxy⟩ := hS.1 x0
    rcases hx0 y hxy with rfl | rfl
    · exact absurd hyS hu
    · exact absurd hyS hw
  · obtain ⟨y, hyS, -⟩ := hS.1 u
    obtain ⟨y', hy'S, hyy'⟩ := hS.1 y
    have h2 : 2 ≤ #S := by
      have := card_le_card (insert_subset hyS (singleton_subset_iff.mpr hy'S))
      rwa [card_pair (G.ne_of_adj hyy')] at this
    have hsub : S ⊆ (univ.erase u).erase w := by
      intro z hz
      simp only [mem_erase, mem_univ, and_true]
      exact ⟨fun h => hw (h ▸ hz), fun h => hu (h ▸ hz)⟩
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm huw, mem_univ w⟩), card_erase_of_mem (mem_univ u),
      card_univ] at this
    omega

/-- **WOWII Conjecture 325.** -/
theorem conjecture325 : Conjecture325 := by
  intro V _ G hG hn ⟨e, he, hle⟩
  induction e using Sym2.ind with
  | h u w =>
  have hc : Gᶜ.Adj u w := mem_edgeFinset.mp he
  obtain ⟨huw, hnadj⟩ := (compl_adj G u w).mp hc
  set X := univ.filter fun z => G.Adj u z ∧ G.Adj w z with hX
  have hsum := complNbr_add_common G huw hnadj
  rw [← hX] at hsum
  set R := ((univ \ X).erase u).erase w with hRdef
  have huX : u ∉ X := by simp [hX]
  have hwX : w ∉ X := by simp [hX]
  have hmemR : ∀ z, z ∈ R ↔ z ≠ w ∧ z ≠ u ∧ z ∉ X := by
    intro z
    simp [hRdef]
  have hRcard : #R + 2 + #X = Fintype.card V := by
    have h1 : #R + 1 = #((univ \ X).erase u) :=
      card_erase_add_one (mem_erase.mpr ⟨Ne.symm huw, mem_sdiff.mpr ⟨mem_univ w, hwX⟩⟩)
    have h2 : #((univ \ X).erase u) + 1 = #(univ \ X) :=
      card_erase_add_one (mem_sdiff.mpr ⟨mem_univ u, huX⟩)
    have h3 : #(univ \ X) = Fintype.card V - #X := by
      rw [card_sdiff_of_subset (subset_univ X), card_univ]
    have h4 := card_le_univ X
    omega
  have hRc : #R + 1 ≤ numComp G (closedNbhd G (degTwo G)) := by omega
  -- the structure: `R = ∅`, plus a vertex adjacent only to `u` and `w` or `n ≤ 4`
  suffices hstruct : #R = 0 ∧
      ((∃ x0, x0 ≠ u ∧ x0 ≠ w ∧ ∀ y, G.Adj x0 y → y = u ∨ y = w) ∨ Fintype.card V ≤ 4) by
    have hR' : ∀ z, z ≠ u → z ≠ w → G.Adj u z ∧ G.Adj w z := by
      intro z hzu hzw
      by_contra h
      have hz : z ∈ R := (hmemR z).mpr ⟨hzw, hzu, by simpa [hX] using h⟩
      rw [card_eq_zero.mp hstruct.1] at hz
      exact notMem_empty z hz
    have h2 := two_of_struct G huw hnadj hR' hstruct.2
    intro S T hS hT
    rw [h2 S hS, h2 T hT]
  by_cases hA : ∃ s0 ∈ X, G.degree s0 = 2
  · obtain ⟨s0, hs0X, hs0deg⟩ := hA
    have hs0 : G.Adj u s0 ∧ G.Adj w s0 := by simpa [hX] using hs0X
    -- the neighbours of `s0` are exactly `u` and `w`
    have hnb : G.neighborFinset s0 = {u, w} := by
      refine (eq_of_subset_of_card_le (fun y hy => ?_) ?_).symm
      · simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact (mem_neighborFinset G s0 _).mpr hs0.1.symm
        · exact (mem_neighborFinset G s0 _).mpr hs0.2.symm
      · rw [card_neighborFinset_eq_degree, hs0deg, card_pair huw]
    have hx0 : ∀ y, G.Adj s0 y → y = u ∨ y = w := by
      intro y hy
      have : y ∈ G.neighborFinset s0 := (mem_neighborFinset G s0 y).mpr hy
      simpa [hnb] using this
    have huNS : u ∈ (closedNbhd G (degTwo G) : Set V) := mem_NS_of_adj G hs0deg hs0.1
    have hwNS : w ∈ (closedNbhd G (degTwo G) : Set V) := mem_NS_of_adj G hs0deg hs0.2
    have hs0NS : s0 ∈ (closedNbhd G (degTwo G) : Set V) := mem_NS_of_deg G hs0deg
    set H := G.induce (closedNbhd G (degTwo G) : Set V)
    set C0 := H.connectedComponentMk ⟨u, huNS⟩
    have hwC0 : H.connectedComponentMk ⟨w, hwNS⟩ = C0 := by
      refine ConnectedComponent.eq.mpr ?_
      exact (Adj.reachable (G := H) (u := ⟨w, hwNS⟩) (v := ⟨s0, hs0NS⟩) hs0.2).trans
        (Adj.reachable (G := H) (u := ⟨s0, hs0NS⟩) (v := ⟨u, huNS⟩) hs0.1.symm)
    -- vertices outside the component of `u` lie in `R`
    have hoff : #(univ.filter fun v => H.connectedComponentMk v ≠ C0) ≤ #R := by
      refine card_le_card_of_injOn (fun v => v.1) (fun v hv => ?_) (fun v _ t _ h => Subtype.ext h)
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hv
      rw [mem_coe, hmemR]
      refine ⟨fun h => hv ?_, fun h => hv ?_, fun h => hv ?_⟩
      · rw [← hwC0]
        congr 1
        exact Subtype.ext h
      · show H.connectedComponentMk v = H.connectedComponentMk ⟨u, huNS⟩
        congr 1
        exact Subtype.ext h
      · have hxu : G.Adj v.1 u := (by simpa [hX] using h : G.Adj u v.1 ∧ G.Adj w v.1).1.symm
        exact ConnectedComponent.eq.mpr (Adj.reachable (G := H) (u := v) (v := ⟨u, huNS⟩) hxu)
    have h3 : 3 * (numComp G (closedNbhd G (degTwo G)) - 1) ≤
        #(univ.filter fun v => H.connectedComponentMk v ≠ C0) := three_mul_le_off G C0
    refine ⟨by omega, Or.inl ⟨s0, (G.ne_of_adj hs0.1).symm, (G.ne_of_adj hs0.2).symm, hx0⟩⟩
  · push Not at hA
    by_cases h2 : G.degree u = 2 ∨ G.degree w = 2
    · have hX2 : #X ≤ 2 := by
        rcases h2 with h2 | h2
        · refine (card_le_card fun z hz => ?_).trans (card_neighborFinset_eq_degree G u ▸ h2.le)
          exact (mem_neighborFinset G u z).mpr (by simpa [hX] using hz : G.Adj u z ∧ G.Adj w z).1
        · refine (card_le_card fun z hz => ?_).trans (card_neighborFinset_eq_degree G w ▸ h2.le)
          exact (mem_neighborFinset G w z).mpr (by simpa [hX] using hz : G.Adj u z ∧ G.Adj w z).2
      have h3 := three_mul_numComp_le G
      have h4 := card_le_univ (closedNbhd G (degTwo G))
      refine ⟨by omega, Or.inr (by omega)⟩
    · push Not at h2
      have hsub : degTwo G ⊆ R := by
        intro s hs
        have hdeg : G.degree s = 2 := by simpa [degTwo] using hs
        rw [hmemR]
        refine ⟨fun h => h2.2 (h ▸ hdeg), fun h => h2.1 (h ▸ hdeg), fun h => hA s h hdeg⟩
      have h3 := numComp_le_card G
      have h4 := card_le_card hsub
      omega

/-- **WOWII Conjecture 325**, also for complete graphs. -/
theorem conjecture325' : Conjecture325' := by
  intro V _ G hG hn h
  rcases h with h | h
  · -- `G` is complete: every minimal total dominating set is a pair
    have hadj : ∀ x y, x ≠ y → G.Adj x y := by
      intro x y hxy
      by_contra hn'
      have : s(x, y) ∈ Gᶜ.edgeFinset := mem_edgeFinset.mpr ((compl_adj G x y).mpr ⟨hxy, hn'⟩)
      rw [h] at this
      exact notMem_empty _ this
    have h2 : ∀ S, IsMinTDS G S → #S = 2 := by
      intro S hS
      obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨x, hxS, -⟩ := hS.1 v
      obtain ⟨y, hyS, hxy⟩ := hS.1 x
      refine card_eq_two hS hxS hyS (G.ne_of_adj hxy) fun z => ?_
      by_cases hzx : z = x
      · exact ⟨y, by simp, hzx ▸ hxy⟩
      · exact ⟨x, by simp, hadj z x hzx⟩
    intro S T hS hT
    rw [h2 S hS, h2 T hT]
  · exact conjecture325 V G hG hn h

end WOWII325
