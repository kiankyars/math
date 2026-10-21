import OpenProblem.WOWII96

/-!
# Written on the Wall II, Conjecture 162

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 162.** If `G` is a simple connected graph, then
> `L_s(G) ≥ freq of minimum of λ(v) * FLOOR[1 / δ(G)]`.

Here `L_s` is the maximum number of leaves of a spanning tree, `λ(v) = α(G[N(v)])`, and `δ` is
the minimum degree. The factor `⌊1/δ⌋` is `1` when `δ = 1` and `0` otherwise, so the claim is:
if `δ = 1`, then `L_s(G)` is at least the number of vertices at which `λ` is minimal.

We prove the conjecture (`conjecture162`).

* If `δ = 1`, a vertex of degree one has `λ = 1`, so every vertex `v` minimising `λ` has
  `λ(v) ≤ 1`. Its neighbourhood is then a clique (`v` is *simplicial*).
* If `S` is a set of simplicial vertices, each with a neighbour outside `S`, then
  `L_s(G) ≥ |S|` (`card_le_Ls_of_simplicial`). Attach each `v ∈ S` to one neighbour `p(v) ∉ S`,
  and keep the edges of `G` outside `S`. The resulting spanning subgraph is connected, because
  `G` is and the neighbours of a simplicial vertex are pairwise adjacent. In any spanning tree of
  it, each vertex of `S` is a leaf.
* If some minimiser of `λ` has all its neighbours among the minimisers, then `G` is complete.
  With `δ = 1` this forces `n = 2`, where both sides equal `2`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII162

open SimpleGraph WOWII178

variable {V : Type*} [Fintype V]

/-- The minimum of `λ(v)` over all vertices. -/
def minLocalIndep (G : SimpleGraph V) : ℕ := sInf (Set.range (localIndep G))

/-- `v` is simplicial: its neighbours are pairwise adjacent. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop :=
  ∀ x y, G.Adj v x → G.Adj v y → x ≠ y → G.Adj x y

lemma localIndep_le_degree (G : SimpleGraph V) (v : V) : localIndep G v ≤ G.degree v := by
  obtain ⟨I, hIv, -, hcard⟩ := exists_indep_nbhd G v
  rw [← hcard, ← card_neighborFinset_eq_degree]
  exact card_le_card fun x hx => (G.mem_neighborFinset v x).mpr (hIv x hx)

lemma isSimplicial_of_localIndep_le_one {G : SimpleGraph V} {v : V} (h : localIndep G v ≤ 1) :
    IsSimplicial G v := by
  intro x y hx hy hxy
  by_contra hnadj
  have := WOWII96.card_le_localIndep G v (A := {x, y})
    (by simp only [mem_insert, mem_singleton]; rintro z (rfl | rfl) <;> assumption)
    (by
      simp only [mem_insert, mem_singleton]
      rintro a (rfl | rfl) c (rfl | rfl)
      · exact G.irrefl
      · exact hnadj
      · exact fun h => hnadj h.symm
      · exact G.irrefl)
  rw [card_pair hxy] at this
  omega

omit [Fintype V] in
/-- Reachability in `H` along every edge of a connected `G` makes `H` connected. -/
lemma connected_of_adj_reachable {G H : SimpleGraph V} (hG : G.Connected)
    (h : ∀ a b, G.Adj a b → H.Reachable a b) : H.Connected := by
  have hw : ∀ {x y : V} (q : G.Walk x y), H.Reachable x y := by
    intro x y q
    induction q with
    | nil => rfl
    | cons hab _ ih => exact (h _ _ hab).trans ih
  have : Nonempty V := hG.nonempty
  exact ⟨fun x y => hw (hG.preconnected x y).some⟩

/-- If every vertex of `S` is simplicial and has a neighbour outside `S`, then `L_s(G) ≥ |S|`. -/
lemma card_le_Ls_of_simplicial {G : SimpleGraph V} (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (S : Finset V) (hS : ∀ v ∈ S, IsSimplicial G v) (hC : ∀ v ∈ S, ∃ w ∉ S, G.Adj v w) :
    #S ≤ Ls G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  -- a neighbour outside `S` for each vertex of `S`
  let p : V → V := fun v => if hv : v ∈ S then (hC v hv).choose else v
  have hp : ∀ v ∈ S, p v ∉ S ∧ G.Adj v (p v) := by
    intro v hv
    simp only [p, hv, dite_true]
    exact (hC v hv).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ ((a ∉ S ∧ b ∉ S) ∨ (a ∈ S ∧ b = p a) ∨ (b ∈ S ∧ a = p b))
      symm := ⟨fun a b h => ⟨h.1.symm, by tauto⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ }
  have hHG : H ≤ G := fun a b h => h.1
  -- an edge from `S` to the outside joins `H`-reachable vertices
  have hmix : ∀ a b, a ∈ S → b ∉ S → G.Adj a b → H.Reachable a b := by
    intro a b ha hb hab
    have h1 : H.Adj a (p a) := ⟨(hp a ha).2, Or.inr (Or.inl ⟨ha, rfl⟩)⟩
    by_cases hb' : b = p a
    · rw [hb']; exact h1.reachable
    · have h2 : H.Adj (p a) b :=
        ⟨hS a ha (p a) b (hp a ha).2 hab (Ne.symm hb'), Or.inl ⟨(hp a ha).1, hb⟩⟩
      exact h1.reachable.trans h2.reachable
  have hH : H.Connected := by
    refine connected_of_adj_reachable hG fun a b hab => ?_
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · have h1 : H.Adj a (p a) := ⟨(hp a ha).2, Or.inr (Or.inl ⟨ha, rfl⟩)⟩
      have hne : p a ≠ b := fun h => (hp a ha).1 (h ▸ hb)
      have h2 := hmix b (p a) hb (hp a ha).1 (hS a ha b (p a) hab (hp a ha).2 hne.symm)
      exact h1.reachable.trans h2.symm
    · exact hmix a b ha hb hab
    · exact (hmix b a hb ha hab.symm).symm
    · exact (show H.Adj a b from ⟨hab, Or.inl ⟨ha, hb⟩⟩).reachable
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  -- every vertex of `S` is a leaf of `T`
  have hleaf : ∀ v ∈ S, T.degree v = 1 := by
    intro v hv
    have hpos := hT.connected.preconnected.degree_pos_of_nontrivial v
    have hle : T.degree v ≤ 1 := by
      rw [← card_neighborFinset_eq_degree, ← card_singleton (p v)]
      apply card_le_card
      intro w hw
      obtain ⟨-, h⟩ := hTH ((T.mem_neighborFinset v w).mp hw)
      rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨hw', h⟩
      · exact absurd hv h
      · exact mem_singleton.mpr h
      · exact absurd (h ▸ hv) (hp w hw').1
    omega
  have h1 : #S ≤ numLeaves T := card_le_card fun v hv => by
    simp only [mem_filter, mem_univ, true_and]; exact hleaf v hv
  exact h1.trans (le_Ls (hTH.trans hHG) hT)

/-- A tree has at least two leaves, so `L_s(G) ≥ 2`. -/
lemma two_le_Ls {G : SimpleGraph V} (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 ≤ Ls G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  have h := sum_degree_le hT ∅
  rw [sum_empty, card_empty] at h
  exact (by omega : 2 ≤ numLeaves T).trans (le_Ls hTG hT)

/-- **WOWII Conjecture 162.** For every connected graph on at least two vertices,
`L_s(G) ≥ (freq of min λ) · ⌊1/δ(G)⌋`. -/
theorem conjecture162 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    #(univ.filter fun v => localIndep G v = minLocalIndep G) * (1 / G.minDegree) ≤ Ls G := by
  have : Nonempty V := hG.nonempty
  by_cases hδ : G.minDegree = 1
  swap
  · have : 1 / G.minDegree = 0 := by
      rcases Nat.lt_or_gt_of_ne hδ with h | h
      · rw [show G.minDegree = 0 by omega, Nat.div_zero]
      · exact Nat.div_eq_of_lt h
    rw [this, mul_zero]
    exact Nat.zero_le _
  rw [hδ, Nat.div_one, mul_one]
  set S := univ.filter fun v => localIndep G v = minLocalIndep G
  -- the minimum of `λ` is at most one
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hm : minLocalIndep G ≤ 1 :=
    (Nat.sInf_le (Set.mem_range_self u)).trans ((localIndep_le_degree G u).trans (by omega))
  have hS : ∀ v ∈ S, IsSimplicial G v := by
    intro v hv
    apply isSimplicial_of_localIndep_le_one
    rw [(mem_filter.mp hv).2]
    exact hm
  by_cases hn2 : Fintype.card V = 2
  · exact (card_le_univ S).trans (hn2 ▸ two_le_Ls hG hn)
  apply card_le_Ls_of_simplicial hG hn S hS
  intro v hv
  by_contra hno
  push Not at hno
  have hno' : ∀ w, G.Adj v w → w ∈ S := fun w hw => by
    by_contra h
    exact hno w h hw
  -- otherwise `v` is adjacent to every other vertex
  have hcl : ∀ a b, G.Adj a b → a ∈ {x | x = v ∨ G.Adj v x} → b ∈ {x | x = v ∨ G.Adj v x} := by
    rintro a b hab (rfl | hva)
    · exact Or.inr hab
    · by_cases hbv : b = v
      · exact Or.inl hbv
      · exact Or.inr (hS a (hno' a hva) v b hva.symm hab (Ne.symm hbv))
  have huniv : ∀ c, c ≠ v → G.Adj v c := by
    intro c hc
    by_contra hvc
    exact not_reachable_of_closed {x | x = v ∨ G.Adj v x} (Or.inl rfl)
      (by rintro (h | h) <;> contradiction) hcl (hG.preconnected v c)
  -- so the vertex `u` of degree one has two neighbours, a contradiction
  have hdu : G.degree u = 1 := by omega
  have h3 : 3 ≤ Fintype.card V := by omega
  have huv : u ≠ v := by
    intro h
    have : G.neighborFinset v = univ.erase v := by
      ext c
      simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
      exact ⟨fun h => (G.ne_of_adj h).symm, huniv c⟩
    rw [h, ← card_neighborFinset_eq_degree, this, card_erase_of_mem (mem_univ v),
      card_univ] at hdu
    omega
  obtain ⟨w, hwu, hwv⟩ : ∃ w, w ≠ u ∧ w ≠ v := by
    by_contra hno''
    push Not at hno''
    have : (univ : Finset V) ⊆ {u, v} := fun c _ => by
      by_cases hc : c = u
      · simp [hc]
      · simp [hno'' c hc]
    have := card_le_card this
    rw [card_univ] at this
    have := card_le_two (a := u) (b := v)
    omega
  have huw : G.Adj u w := hS v hv u w (huniv u huv) (huniv w hwv) (Ne.symm hwu)
  have hsub : ({v, w} : Finset V) ⊆ G.neighborFinset u := by
    intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact (G.mem_neighborFinset u c).mpr (huniv u huv).symm
    · exact (G.mem_neighborFinset u c).mpr huw
  have := card_le_card hsub
  rw [card_pair (Ne.symm hwv), card_neighborFinset_eq_degree] at this
  omega

end WOWII162
