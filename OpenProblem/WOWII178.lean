import Mathlib

/-!
# Written on the Wall II, Conjecture 178

E. DeLaViña's *Written on the Wall II* (conjectures of Graffiti.pc) lists as open:

> **Conjecture 178.** If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ maximum of λ(v) + maximum of {|N(e)| : e an edge of G}`.

Here `L_s(G)` is the maximum number of leaves of a spanning tree of `G`, `b(G)` is the order of
a largest induced bipartite subgraph, `λ(v)` is the independence number of the subgraph induced
by the neighbourhood of `v`, and `N(e) = N(u) ∪ N(v)` for an edge `e = uv`. (This set contains
`u` and `v`, matching the page's remark that `L_s(G) ≥ |N(e)| - 2`. Reading `|N(e)|` as the
number of vertices other than `u` and `v` only weakens the statement.)

We prove the conjecture (`conjecture178`). The page notes that `L_s(G) ≥ |N(e)| - 2` and
`b(G) ≥ λ(v) + 1`, which give the bound up to one. The missing one comes from `b`: if `v` is
not adjacent to some vertex `w ≠ v`, then `{v, w}` together with an independent set in `N(v)`
induces a bipartite graph, so `b(G) ≥ λ(v) + 2`. If instead `v` is adjacent to every other
vertex, then `L_s(G) = n - 1`, and `|N(e)| ≤ n` finishes the bound.

The bound `L_s(G) ≥ |N(e)| - 2` is proved by extending the double star on `e` to a spanning
tree `T` (Mathlib's `Connected.exists_isTree_le_of_le_of_isAcyclic`) and counting leaves with
the degree sum: in a tree, `deg u + deg v ≤ #leaves + 2` for distinct `u`, `v`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII178

variable {V : Type*} [Fintype V]

open SimpleGraph

/-! ### The invariants -/

/-- The number of leaves (vertices of degree one) of a graph. -/
def numLeaves (T : SimpleGraph V) : ℕ := #{v | T.degree v = 1}

/-- `L_s(G)`: the maximum number of leaves of a spanning tree of `G`. -/
def Ls (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ numLeaves T = k}

/-- `b(G)`: the order of a largest induced bipartite subgraph of `G`. -/
def b (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ #s = k}

/-- `λ(v)`: the independence number of the subgraph induced by the neighbourhood of `v`. -/
def localIndep (G : SimpleGraph V) (v : V) : ℕ := (G.induce (G.neighborSet v)).indepNum

/-- The maximum of `λ(v)` over all vertices. -/
def maxLocalIndep (G : SimpleGraph V) : ℕ := univ.sup (localIndep G)

/-- `|N(e)|` for the edge `e = uv`, where `N(e) = N(u) ∪ N(v)`. -/
def edgeNbhd (G : SimpleGraph V) (u v : V) : ℕ := #(G.neighborFinset u ∪ G.neighborFinset v)

/-- The maximum of `|N(e)|` over all edges `e` of `G`. -/
def maxEdgeNbhd (G : SimpleGraph V) : ℕ :=
  ({p | G.Adj p.1 p.2} : Finset (V × V)).sup fun p => edgeNbhd G p.1 p.2

/-! ### Counting leaves of a tree -/

lemma sum_degree_add_two {T : SimpleGraph V} (hT : T.IsTree) :
    ∑ v, T.degree v + 2 = 2 * Fintype.card V := by
  have h1 := T.sum_degrees_eq_twice_card_edges
  have h2 := hT.card_edgeFinset
  omega

omit [Fintype V] in
lemma sum_ite_one_two (A : Finset V) (p : V → Prop) [DecidablePred p] :
    ∑ x ∈ A, (if p x then 1 else 2) + #(A.filter p) = 2 * #A := by
  rw [Finset.card_eq_sum_ones (A.filter p), Finset.sum_filter, ← Finset.sum_add_distrib,
    Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

/-- In a tree with at least two vertices, the degrees over any vertex set `S` satisfy
`∑_{x ∈ S} deg x + 2 ≤ 2|S| + #leaves`. -/
lemma sum_degree_le {T : SimpleGraph V} (hT : T.IsTree) [Nontrivial V] (S : Finset V) :
    ∑ x ∈ S, T.degree x + 2 ≤ 2 * #S + numLeaves T := by
  have hpos : ∀ x, 0 < T.degree x := fun x => hT.connected.preconnected.degree_pos_of_nontrivial x
  have h1 : ∑ x ∈ S, T.degree x + ∑ x ∈ Sᶜ, T.degree x = ∑ x, T.degree x :=
    Finset.sum_add_sum_compl S _
  have h2 := sum_degree_add_two hT
  have h3 : ∑ x ∈ Sᶜ, (if T.degree x = 1 then 1 else 2) ≤ ∑ x ∈ Sᶜ, T.degree x := by
    apply Finset.sum_le_sum
    intro x _
    have := hpos x
    split_ifs <;> omega
  have h4 := sum_ite_one_two Sᶜ (fun x => T.degree x = 1)
  have h5 : #(Sᶜ.filter fun x => T.degree x = 1) ≤ numLeaves T := by
    unfold numLeaves
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have h6 : #S + #Sᶜ = Fintype.card V := Finset.card_add_card_compl S
  omega

/-! ### Lower bound for `L_s` -/

lemma numLeaves_le_card (T : SimpleGraph V) : numLeaves T ≤ Fintype.card V := by
  unfold numLeaves
  exact Finset.card_le_univ _

lemma le_Ls {G T : SimpleGraph V} (hle : T ≤ G) (hT : T.IsTree) : numLeaves T ≤ Ls G := by
  apply le_csSup
  · exact ⟨Fintype.card V, by rintro k ⟨T', -, -, rfl⟩; exact numLeaves_le_card T'⟩
  · exact ⟨T, hle, hT, rfl⟩

omit [Fintype V] in
/-- If `C` contains `a`, misses `b`, and is closed under adjacency, then `b` is not reachable
from `a`. -/
lemma not_reachable_of_closed {K : SimpleGraph V} {a c : V} (C : Set V) (ha : a ∈ C)
    (hc : c ∉ C) (hC : ∀ x y, K.Adj x y → x ∈ C → y ∈ C) : ¬ K.Reachable a c := by
  rintro ⟨p⟩
  suffices ∀ {x y : V} (q : K.Walk x y), x ∈ C → y ∈ C from hc (this p ha)
  intro x y q
  induction q with
  | nil => exact id
  | cons h _ ih => exact fun hx => ih (hC _ _ h hx)

section DoubleStar

variable (G : SimpleGraph V) (u v : V)

/-- The double star on the edge `uv`: `u` is joined to all of its neighbours, and `v` is joined
to its neighbours that are neither `u` nor neighbours of `u`. -/
def doubleStar : SimpleGraph V :=
  fromEdgeSet ({e | ∃ x, G.Adj u x ∧ e = s(u, x)} ∪
    {e | ∃ y, G.Adj v y ∧ ¬ G.Adj u y ∧ y ≠ u ∧ e = s(v, y)})

variable {G u v}

omit [Fintype V] in
lemma doubleStar_adj {a c : V} :
    (doubleStar G u v).Adj a c ↔
      ((a = u ∧ G.Adj u c) ∨ (c = u ∧ G.Adj u a)) ∨
      ((a = v ∧ G.Adj v c ∧ ¬ G.Adj u c ∧ c ≠ u) ∨ (c = v ∧ G.Adj v a ∧ ¬ G.Adj u a ∧ a ≠ u)) := by
  unfold doubleStar
  rw [fromEdgeSet_adj]
  simp only [Set.mem_union, Set.mem_ofPred_eq, Sym2.eq_iff]
  constructor
  · rintro ⟨(⟨x, hx, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨y, hy, hy', hy'', (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩), -⟩
    · exact Or.inl (Or.inl ⟨rfl, hx⟩)
    · exact Or.inl (Or.inr ⟨rfl, hx⟩)
    · exact Or.inr (Or.inl ⟨rfl, hy, hy', hy''⟩)
    · exact Or.inr (Or.inr ⟨rfl, hy, hy', hy''⟩)
  · rintro ((⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h, h', h''⟩ | ⟨rfl, h, h', h''⟩))
    · exact ⟨Or.inl ⟨c, h, Or.inl ⟨rfl, rfl⟩⟩, h.ne⟩
    · exact ⟨Or.inl ⟨a, h, Or.inr ⟨rfl, rfl⟩⟩, h.ne.symm⟩
    · exact ⟨Or.inr ⟨c, h, h', h'', Or.inl ⟨rfl, rfl⟩⟩, h.ne⟩
    · exact ⟨Or.inr ⟨a, h, h', h'', Or.inr ⟨rfl, rfl⟩⟩, h.ne.symm⟩

omit [Fintype V] in
lemma doubleStar_le : doubleStar G u v ≤ G := by
  intro a c h
  rcases doubleStar_adj.mp h with ((⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h, -⟩ | ⟨rfl, h, -⟩))
  · exact h
  · exact h.symm
  · exact h
  · exact h.symm

omit [Fintype V] in
lemma doubleStar_isBridge_u (huv : G.Adj u v) {x : V} (hx : G.Adj u x) :
    (doubleStar G u v).IsBridge s(u, x) := by
  rw [isBridge_iff]
  by_cases hxv : x = v
  · subst hxv
    refine not_reachable_of_closed {y | y = u ∨ (G.Adj u y ∧ y ≠ x)} (Or.inl rfl) ?_ ?_
    · rintro (h | ⟨-, h⟩)
      · exact hx.ne h.symm
      · exact h rfl
    · intro a c hac ha
      rw [deleteEdges_adj, Set.mem_singleton_iff] at hac
      obtain ⟨hac, hne⟩ := hac
      rcases ha with rfl | ⟨hua, hax⟩
      · rcases doubleStar_adj.mp hac with ((⟨-, h⟩ | ⟨rfl, h⟩) | (⟨h, -⟩ | ⟨rfl, -, -, h⟩))
        · refine Or.inr ⟨h, ?_⟩
          rintro rfl
          exact hne rfl
        · exact absurd h G.irrefl
        · exact absurd h hx.ne
        · exact absurd rfl h
      · rcases doubleStar_adj.mp hac with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨rfl, -⟩ | ⟨-, -, h, -⟩))
        · exact absurd hua G.irrefl
        · exact Or.inl rfl
        · exact absurd rfl hax
        · exact absurd hua h
  · refine fun hr => not_reachable_of_closed {x} (Set.mem_singleton x)
      (fun h => hx.ne (Set.mem_singleton_iff.mp h)) ?_ hr.symm
    intro a c hac ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hac
    obtain ⟨hac, hne⟩ := hac
    rcases doubleStar_adj.mp hac with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨rfl, -⟩ | ⟨-, -, h, -⟩))
    · exact absurd hx G.irrefl
    · exact absurd Sym2.eq_swap hne
    · exact absurd rfl hxv
    · exact absurd hx h

omit [Fintype V] in
lemma doubleStar_isBridge_v {y : V} (hy : G.Adj v y) (hy' : ¬ G.Adj u y) (hy'' : y ≠ u) :
    (doubleStar G u v).IsBridge s(v, y) := by
  rw [isBridge_iff]
  refine fun hr => not_reachable_of_closed {y} (Set.mem_singleton y)
    (fun h => hy.ne (Set.mem_singleton_iff.mp h)) ?_ hr.symm
  intro a c hac ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rw [deleteEdges_adj, Set.mem_singleton_iff] at hac
  obtain ⟨hac, hne⟩ := hac
  rcases doubleStar_adj.mp hac with ((⟨rfl, -⟩ | ⟨rfl, h⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩))
  · exact absurd rfl hy''
  · exact absurd h hy'
  · exact absurd hy G.irrefl
  · exact absurd Sym2.eq_swap hne

omit [Fintype V] in
lemma doubleStar_isAcyclic (huv : G.Adj u v) : (doubleStar G u v).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a c hac
  rcases doubleStar_adj.mp hac with
    ((⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h, h', h''⟩ | ⟨rfl, h, h', h''⟩))
  · exact doubleStar_isBridge_u huv h
  · rw [Sym2.eq_swap]; exact doubleStar_isBridge_u huv h
  · exact doubleStar_isBridge_v h h' h''
  · rw [Sym2.eq_swap]; exact doubleStar_isBridge_v h h' h''

omit [Fintype V] in
/-- A spanning tree containing the double star on the edge `uv`. -/
lemma exists_tree_doubleStar (hG : G.Connected) (huv : G.Adj u v) :
    ∃ T ≤ G, T.IsTree ∧ (∀ x, G.Adj u x → T.Adj u x) ∧
      (∀ y, G.Adj v y → T.Adj u y ∨ T.Adj v y) := by
  obtain ⟨T, hHT, hTG, hT⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic doubleStar_le (doubleStar_isAcyclic huv)
  have hu : ∀ x, G.Adj u x → T.Adj u x :=
    fun x hx => hHT (doubleStar_adj.mpr (Or.inl (Or.inl ⟨rfl, hx⟩)))
  refine ⟨T, hTG, hT, hu, fun y hy => ?_⟩
  by_cases h1 : G.Adj u y
  · exact Or.inl (hu y h1)
  by_cases h2 : y = u
  · subst h2
    exact Or.inr (hu v huv).symm
  · exact Or.inr (hHT (doubleStar_adj.mpr (Or.inr (Or.inl ⟨rfl, hy, h1, h2⟩))))

end DoubleStar

/-- `L_s(G) + 2 ≥ |N(e)|` for every edge `e` of a connected graph. -/
lemma edgeNbhd_le_Ls_add_two {G : SimpleGraph V} (hG : G.Connected) {u v : V}
    (huv : G.Adj u v) : edgeNbhd G u v ≤ Ls G + 2 := by
  have : Nontrivial V := ⟨⟨u, v, huv.ne⟩⟩
  obtain ⟨T, hTG, hT, hu, hv⟩ := exists_tree_doubleStar hG huv
  have hsub :
      G.neighborFinset u ∪ G.neighborFinset v ⊆ T.neighborFinset u ∪ T.neighborFinset v := by
    intro y hy
    simp only [Finset.mem_union, mem_neighborFinset] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (hu y hy)
    · exact hv y hy
  have h1 : edgeNbhd G u v ≤ T.degree u + T.degree v := by
    unfold edgeNbhd
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := sum_degree_le hT {u, v}
  rw [Finset.sum_pair huv.ne, Finset.card_pair huv.ne] at h2
  have h3 := le_Ls hTG hT
  omega

/-- If `v` is adjacent to every other vertex, then `L_s(G) ≥ n - 1`. -/
lemma card_sub_one_le_Ls {G : SimpleGraph V} (hG : G.Connected) [Nontrivial V] {v : V}
    (hv : ∀ w, w ≠ v → G.Adj v w) : Fintype.card V - 1 ≤ Ls G := by
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨T, hTG, hT, hu, -⟩ := exists_tree_doubleStar hG (hv w hw)
  have hdeg : Fintype.card V - 1 ≤ T.degree v := by
    have : #(univ.erase v) ≤ #(T.neighborFinset v) := by
      apply Finset.card_le_card
      intro x hx
      rw [mem_neighborFinset]
      exact hu x (hv x (Finset.ne_of_mem_erase hx))
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      card_neighborFinset_eq_degree] at this
    exact this
  have h2 := sum_degree_le hT {v}
  rw [Finset.sum_singleton, Finset.card_singleton] at h2
  have h3 := le_Ls hTG hT
  omega

/-! ### Lower bounds for `b` -/

lemma card_le_b (G : SimpleGraph V) (S : Finset V) (c : V → Fin 2)
    (hc : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y) : #S ≤ b G := by
  apply le_csSup
  · exact ⟨Fintype.card V, by rintro k ⟨s, -, rfl⟩; exact Finset.card_le_univ s⟩
  · refine ⟨S, ⟨Coloring.mk (fun x => c x.1) fun {x y} h => hc x.1 x.2 y.1 y.2 h⟩, rfl⟩

omit [Fintype V] in
/-- An independent set in `N(v)` of size `λ(v)`. -/
lemma exists_indep_nbhd (G : SimpleGraph V) (v : V) :
    ∃ I : Finset V, (∀ x ∈ I, G.Adj v x) ∧ (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧
      #I = localIndep G v := by
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x', -, rfl⟩ := Finset.mem_map.mp hx
    exact x'.2
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    have hne : x' ≠ y' := by
      rintro rfl
      exact G.irrefl hxy
    exact hs.isIndepSet hx' hy' hne hxy
  · rw [Finset.card_map]
    exact hs.card_eq

lemma localIndep_add_one_le_b (G : SimpleGraph V) (v : V) : localIndep G v + 1 ≤ b G := by
  obtain ⟨I, hIv, hII, hcard⟩ := exists_indep_nbhd G v
  have hvI : v ∉ I := fun h => G.irrefl (hIv v h)
  have := card_le_b G (insert v I) (fun x => if x = v then 0 else 1) ?_
  · rw [Finset.card_insert_of_notMem hvI] at this
    omega
  · intro x hx y hy hxy heq
    rw [Finset.mem_insert] at hx hy
    by_cases hxv : x = v <;> by_cases hyv : y = v
    · rw [hxv, hyv] at hxy
      exact G.irrefl hxy
    · simp [hxv, hyv] at heq
    · simp [hxv, hyv] at heq
    · exact hII x (hx.resolve_left hxv) y (hy.resolve_left hyv) hxy

lemma localIndep_add_two_le_b (G : SimpleGraph V) {v w : V} (hwv : w ≠ v) (hvw : ¬ G.Adj v w) :
    localIndep G v + 2 ≤ b G := by
  obtain ⟨I, hIv, hII, hcard⟩ := exists_indep_nbhd G v
  have hwI : w ∉ I := fun h => hvw (hIv w h)
  have hvI : v ∉ insert w I := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hwv h.symm
    · exact G.irrefl (hIv v h)
  have := card_le_b G (insert v (insert w I)) (fun x => if x = v ∨ x = w then 0 else 1) ?_
  · rw [Finset.card_insert_of_notMem hvI, Finset.card_insert_of_notMem hwI] at this
    omega
  · intro x hx y hy hxy heq
    simp only [Finset.mem_insert] at hx hy
    by_cases hxv : x = v ∨ x = w <;> by_cases hyv : y = v ∨ y = w
    · rcases hxv with rfl | rfl <;> rcases hyv with rfl | rfl
      · exact G.irrefl hxy
      · exact hvw hxy
      · exact hvw hxy.symm
      · exact G.irrefl hxy
    · simp [hxv, hyv] at heq
    · simp [hxv, hyv] at heq
    · have hxI : x ∈ I := by tauto
      have hyI : y ∈ I := by tauto
      exact hII x hxI y hyI hxy

/-! ### The conjecture -/

/-- **WOWII Conjecture 178.** For a connected graph `G` on at least two vertices,
`L_s(G) + b(G) ≥ max_v λ(v) + max_{uv ∈ E(G)} |N(u) ∪ N(v)|`. -/
theorem conjecture178 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    maxLocalIndep G + maxEdgeNbhd G ≤ Ls G + b G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨v₀, -, hv₀⟩ := Finset.exists_mem_eq_sup univ univ_nonempty (localIndep G)
  have hmax : maxLocalIndep G = localIndep G v₀ := hv₀
  -- an edge exists
  obtain ⟨x₀, y₀, hxy₀⟩ : ∃ x y, G.Adj x y := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    obtain ⟨y, hy⟩ := G.degree_pos_iff_exists_adj x |>.mp
      (hG.preconnected.degree_pos_of_nontrivial x)
    exact ⟨x, y, hy⟩
  have hne : ({p | G.Adj p.1 p.2} : Finset (V × V)).Nonempty :=
    ⟨(x₀, y₀), by simpa using hxy₀⟩
  obtain ⟨⟨u₁, w₁⟩, hp, hp'⟩ := Finset.exists_mem_eq_sup _ hne fun p => edgeNbhd G p.1 p.2
  have hadj : G.Adj u₁ w₁ := by simpa using hp
  have hedge : maxEdgeNbhd G = edgeNbhd G u₁ w₁ := hp'
  by_cases huniv : ∀ w, w ≠ v₀ → G.Adj v₀ w
  · -- `v₀` is adjacent to every other vertex
    have h1 := card_sub_one_le_Ls hG huniv
    have h2 := localIndep_add_one_le_b G v₀
    have h3 : edgeNbhd G u₁ w₁ ≤ Fintype.card V := Finset.card_le_univ _
    omega
  · push Not at huniv
    obtain ⟨w, hwv, hvw⟩ := huniv
    have h1 := edgeNbhd_le_Ls_add_two hG hadj
    have h2 := localIndep_add_two_le_b G hwv hvw
    omega

end WOWII178
