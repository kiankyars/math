import OpenProblem.WOWII422b

/-!
# Written on the Wall II, Conjecture 426

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 426.** Let `G` be a connected graph on `n > 3` vertices and `M` the vertices of
> maximum degree. Then `i(G) ≤ n - γ(G[N(M)])`.

Here `i` is the independent domination number and `γ` the domination number.

We prove the conjecture for every finite graph (`conjecture426`), with `M` any set of vertices.

* Let `J` be a maximal independent subset of `M`, and extend it to a maximal independent set `I`
  of `G`. Then `I` is an independent dominating set.
* `N(M) \ I` dominates `G[N(M)]`. Let `x ∈ N(M) ∩ I` be adjacent to `m ∈ M`. Then `m ∉ J`,
  since `I` is independent. By maximality of `J`, `m` has a neighbour in `J ⊆ I`. So `m ∉ I`
  and `m ∈ N(M)`.

Hence `i(G) + γ(G[N(M)]) ≤ |I| + |N(M) \ I| ≤ n`.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII426

open WOWII179 WOWII422b

variable {V : Type*} [Fintype V]

/-- The open neighbourhood `N(M)` of a set. -/
def nbhd (G : SimpleGraph V) (M : Finset V) : Finset V := univ.filter fun v => ∃ m ∈ M, G.Adj v m

/-- The statement of Conjecture 426. -/
def Conjecture426 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    indepDomNum G + domNum (G.induce (nbhd G (maxDegSet G) : Set V)) ≤ Fintype.card V

/-- A maximal independent set containing a given independent set. -/
lemma exists_maximal_indep (G : SimpleGraph V) (J : Finset V) (hJ : IsIndep G J) :
    ∃ I, J ⊆ I ∧ IsIndep G I ∧ ∀ x ∉ I, ∃ u ∈ I, G.Adj x u := by
  let F : Finset (Finset V) := univ.filter fun I => J ⊆ I ∧ IsIndep G I
  have hF : J ∈ F := by simp [F, hJ]
  obtain ⟨I, hIF, hImax⟩ := F.exists_max_image card ⟨_, hF⟩
  simp only [F, mem_filter, mem_univ, true_and] at hIF
  refine ⟨I, hIF.1, hIF.2, fun x hx => ?_⟩
  by_contra hno
  push Not at hno
  have hins : insert x I ∈ F := by
    simp only [F, mem_filter, mem_univ, true_and]
    refine ⟨hIF.1.trans (subset_insert x I), ?_⟩
    intro a ha b hb hab
    simp only [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact G.irrefl hab
    · exact hno b hb hab
    · exact hno a ha hab.symm
    · exact hIF.2 a ha b hb hab
  have := hImax _ hins
  rw [card_insert_of_notMem hx] at this
  omega

/-- `i(G) + γ(G[N(M)]) ≤ n` for every set `M`. -/
theorem indepDomNum_add_domNum_le (G : SimpleGraph V) (M : Finset V) :
    indepDomNum G + domNum (G.induce (nbhd G M : Set V)) ≤ Fintype.card V := by
  -- a maximal independent subset of `M`
  obtain ⟨J, hJM, hJind, hJmax⟩ : ∃ J ⊆ M, IsIndep G J ∧ ∀ m ∈ M, m ∉ J → ∃ j ∈ J, G.Adj m j := by
    let F : Finset (Finset V) := M.powerset.filter fun J => IsIndep G J
    have hF : ∅ ∈ F := mem_filter.mpr ⟨empty_mem_powerset M, fun x hx => absurd hx (notMem_empty x)⟩
    obtain ⟨J, hJF, hJmax⟩ := F.exists_max_image card ⟨_, hF⟩
    simp only [F, mem_filter, mem_powerset] at hJF
    refine ⟨J, hJF.1, hJF.2, fun m hm hmJ => ?_⟩
    by_contra hno
    push Not at hno
    have hins : insert m J ∈ F := by
      simp only [F, mem_filter, mem_powerset]
      refine ⟨insert_subset hm hJF.1, ?_⟩
      intro a ha b hb hab
      simp only [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact G.irrefl hab
      · exact hno b hb hab
      · exact hno a ha hab.symm
      · exact hJF.2 a ha b hb hab
    have := hJmax _ hins
    rw [card_insert_of_notMem hmJ] at this
    omega
  obtain ⟨I, hJI, hIind, hImax⟩ := exists_maximal_indep G J hJind
  -- `I` is an independent dominating set
  have hI : indepDomNum G ≤ #I := by
    refine Nat.sInf_le (s := {k | ∃ S, IsDom G S ∧ IsIndep G S ∧ #S = k}) ⟨I, ?_, hIind, rfl⟩
    intro x
    by_cases hx : x ∈ I
    · exact Or.inl hx
    · exact Or.inr (hImax x hx)
  -- `N(M) \ I` dominates `G[N(M)]`
  set N := nbhd G M
  let D : Finset (N : Set V) := univ.filter fun x => x.1 ∉ I
  have hD : IsDom (G.induce (N : Set V)) D := by
    intro x
    by_cases hxI : x.1 ∈ I
    · right
      obtain ⟨m, hmM, hxm⟩ := (mem_filter.mp (show x.1 ∈ N from x.2)).2
      have hmJ : m ∉ J := fun h => hIind x.1 hxI m (hJI h) hxm
      obtain ⟨j, hjJ, hmj⟩ := hJmax m hmM hmJ
      have hmI : m ∉ I := fun h => hIind m h j (hJI hjJ) hmj
      have hmN : m ∈ N := mem_filter.mpr ⟨mem_univ m, j, hJM hjJ, hmj⟩
      exact ⟨⟨m, hmN⟩, mem_filter.mpr ⟨mem_univ _, hmI⟩, hxm⟩
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _, hxI⟩)
  have hγ := domNum_le hD
  -- `I` and `N \ I` are disjoint
  have hcard : #D = #(N \ I) := by
    rw [← card_map (Function.Embedding.subtype _)]
    congr 1
    ext y
    simp only [D, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, mem_sdiff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hyN, hyI⟩
      exact ⟨⟨y, hyN⟩, hyI, rfl⟩
  have hdisj : #(N \ I) + #I ≤ Fintype.card V := by
    rw [← card_union_of_disjoint sdiff_disjoint]
    exact card_le_univ _
  omega

/-- **WOWII Conjecture 426.** -/
theorem conjecture426 : Conjecture426 := fun _ _ G _ _ =>
  indepDomNum_add_domNum_le G (maxDegSet G)

end WOWII426
