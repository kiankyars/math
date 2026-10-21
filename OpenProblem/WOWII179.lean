import OpenProblem.WOWII161

/-!
# Written on the Wall II, Conjecture 179

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 179.** If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ Δ(G) + domination(G) + maximum of λ(v)`.

Here `L_s` is the maximum number of leaves of a spanning tree, `b` the order of a largest induced
bipartite subgraph, `γ = domination(G)` the domination number and `λ(v) = α(G[N(v)])`.

We prove the conjecture (`conjecture179`) from two inequalities.

* `L_s ≥ Δ`: a spanning tree containing all edges at a vertex of maximum degree has at least
  `Δ` leaves (`WOWII161.degree_le_Ls`).
* `b ≥ γ + λ_max` (`domNum_add_le_b`): let `u` maximise `λ` and let `J ⊆ N(u)` be independent
  with `|J| = λ(u)`. Extend `{u}` to a maximal independent set `I` of `G - J`. Then `I` dominates
  `G`, and `I ∪ J` is the union of two disjoint independent sets, so it induces a bipartite
  graph.

Both inequalities are sharp for stars.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII179

open SimpleGraph WOWII178

variable {V : Type*} [Fintype V]

/-- `S` is a dominating set. -/
def IsDom (G : SimpleGraph V) (S : Finset V) : Prop := ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj v u

/-- The domination number `γ(G)`. -/
def domNum (G : SimpleGraph V) : ℕ := sInf {k | ∃ S, IsDom G S ∧ #S = k}

omit [Fintype V] in
lemma domNum_le {G : SimpleGraph V} {S : Finset V} (hS : IsDom G S) : domNum G ≤ #S :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- `b(G) ≥ γ(G) + λ(u)` for every vertex `u`. -/
lemma domNum_add_le_b (G : SimpleGraph V) (u : V) : domNum G + localIndep G u ≤ b G := by
  obtain ⟨J, hJu, hJJ, hcard⟩ := exists_indep_nbhd G u
  have huJ : u ∉ J := fun h => G.irrefl (hJu u h)
  -- the independent sets of `G - J` containing `u`
  let F : Finset (Finset V) := univ.filter fun I =>
    u ∈ I ∧ Disjoint I J ∧ ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y
  have hF : {u} ∈ F := by
    simp only [F, mem_filter, mem_univ, true_and, mem_singleton, disjoint_singleton_left]
    exact ⟨huJ, fun x hx y hy => by rw [hx, hy]; exact G.irrefl⟩
  obtain ⟨I, hIF, hImax⟩ := F.exists_max_image card ⟨_, hF⟩
  simp only [F, mem_filter, mem_univ, true_and] at hIF
  obtain ⟨huI, hIJ, hII⟩ := hIF
  -- `I` dominates `G`
  have hdom : IsDom G I := by
    intro x
    by_cases hxI : x ∈ I
    · exact Or.inl hxI
    right
    by_cases hxJ : x ∈ J
    · exact ⟨u, huI, (hJu x hxJ).symm⟩
    by_contra hno
    push Not at hno
    have hins : insert x I ∈ F := by
      simp only [F, mem_filter, mem_univ, true_and, mem_insert]
      refine ⟨Or.inr huI, disjoint_insert_left.mpr ⟨hxJ, hIJ⟩, ?_⟩
      rintro a (rfl | ha) c (rfl | hc)
      · exact G.irrefl
      · exact hno c hc
      · exact fun h => hno a ha h.symm
      · exact hII a ha c hc
    have := hImax _ hins
    rw [card_insert_of_notMem hxI] at this
    omega
  -- `I ∪ J` induces a bipartite graph
  have hb := card_le_b G (I ∪ J) (fun x => if x ∈ J then 1 else 0) (by
    intro x hx y hy hxy heq
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hII x hx y hy hxy
    · have hxJ : x ∉ J := disjoint_left.mp hIJ hx
      simp [hxJ, hy] at heq
    · have hyJ : y ∉ J := disjoint_left.mp hIJ hy
      simp [hyJ, hx] at heq
    · exact hJJ x hx y hy hxy)
  rw [card_union_of_disjoint hIJ, hcard] at hb
  have := domNum_le hdom
  omega

/-- **WOWII Conjecture 179.** For every connected graph on at least two vertices,
`L_s(G) + b(G) ≥ Δ(G) + γ(G) + max λ(v)`. -/
theorem conjecture179 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    G.maxDegree + domNum G + maxLocalIndep G ≤ Ls G + b G := by
  have : Nonempty V := hG.nonempty
  obtain ⟨x, hx⟩ := G.exists_maximal_degree_vertex
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup univ univ_nonempty (localIndep G)
  have h1 := WOWII161.degree_le_Ls hG hn x
  have h2 := domNum_add_le_b G u
  rw [maxLocalIndep, hu, hx]
  omega

end WOWII179
