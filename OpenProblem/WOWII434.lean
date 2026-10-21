import OpenProblem.WOWII422b
import OpenProblem.WOWII318

/-!
# Written on the Wall II, Conjectures 434b and 434c

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 434b.** Let `G` be a connected graph on `n > 3` vertices and `M` the set of
> maximum degree vertices of `G`. Then `i(G) ≤ δ(G[M]) + 1 + SW(G^c)`. If diameter `> 2`, then
> `i(G) ≤ δ(G[M]) + SW(G^c)`.
>
> **Conjecture 434c.** Let `G` be a connected graph on `n > 3` vertices and `M` the set of
> maximum degree vertices of `G`. Then `i(G) ≤ δ(G[V-M]) + 1 + SW(G^c)`. If `δ(G) = 1`, then
> `i(G) ≤ δ(G[V-M]) + SW(G^c)`.

Here `i` is the independent domination number and `SW(H) = 1 + max_X δ(H[X])` is the
Szekeres–Wilf number (the degeneracy plus one).

Both conjectures follow from `i(G) ≤ SW(Ḡ)` (`indepDomNum_le_SW`).

* Let `v` have maximum degree `Δ`. Then `v`, together with a maximal independent set of
  `G - N[v]`, is an independent dominating set, so `i(G) ≤ n - Δ`.
* Taking `X = V` gives `SW(Ḡ) ≥ 1 + δ(Ḡ) = 1 + (n - 1 - Δ) = n - Δ`.

The extra terms `δ(G[M])`, `δ(G[V - M])` and `+ 1` are nonnegative, and the conditions on the
diameter and on `δ(G)` are not needed.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII434

open WOWII179 WOWII422b

variable {V : Type*} [Fintype V]

/-- The minimum degree of `G[X]` (zero for empty `X`). -/
def minDegIn (G : SimpleGraph V) (X : Finset V) : ℕ :=
  if h : X.Nonempty then X.inf' h fun x => #(X.filter (G.Adj x)) else 0

/-- The Szekeres–Wilf number `SW(H) = 1 + max_X δ(H[X])`, the maximum over nonempty `X`. -/
def SW (H : SimpleGraph V) : ℕ :=
  1 + sSup {d | ∃ X : Finset V, X.Nonempty ∧ ∀ x ∈ X, d ≤ #(X.filter (H.Adj x))}

/-- `i(G) ≤ n - Δ(G)`. -/
lemma indepDomNum_le (G : SimpleGraph V) [Nonempty V] :
    indepDomNum G ≤ Fintype.card V - G.maxDegree := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  set R := (G.neighborFinset v)ᶜ.erase v
  -- a maximal independent subset of `R`
  let F : Finset (Finset V) := R.powerset.filter fun I => IsIndep G I
  have hF : ∅ ∈ F := mem_filter.mpr ⟨empty_mem_powerset R, fun x hx => absurd hx (notMem_empty x)⟩
  obtain ⟨J, hJF, hJmax⟩ := F.exists_max_image card ⟨_, hF⟩
  simp only [F, mem_filter, mem_powerset] at hJF
  obtain ⟨hJR, hJind⟩ := hJF
  have hvJ : v ∉ J := fun h => by simpa [R] using hJR h
  have hJN : ∀ x ∈ J, ¬ G.Adj v x := fun x hx h => by
    have := hJR hx
    simp [R, mem_neighborFinset, h] at this
  let I := insert v J
  have hI : IsIndep G I := by
    intro x hx y hy hxy
    simp only [I, mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact G.irrefl hxy
    · exact hJN y hy hxy
    · exact hJN x hx hxy.symm
    · exact hJind x hx y hy hxy
  have hD : IsDom G I := by
    intro x
    by_cases hxI : x ∈ I
    · exact Or.inl hxI
    right
    by_cases hxv : G.Adj x v
    · exact ⟨v, mem_insert_self v J, hxv⟩
    · have hxR : x ∈ R := by
        simp only [R, mem_erase, mem_compl, mem_neighborFinset]
        refine ⟨fun h => hxI (h ▸ mem_insert_self v J), fun h => hxv h.symm⟩
      have hxJ : x ∉ J := fun h => hxI (mem_insert_of_mem h)
      by_contra hno
      push Not at hno
      have hins : insert x J ∈ F := by
        simp only [F, mem_filter, mem_powerset]
        refine ⟨insert_subset hxR hJR, ?_⟩
        intro a ha b hb hab
        simp only [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl hab
        · exact hno b (mem_insert_of_mem hb) hab
        · exact hno a (mem_insert_of_mem ha) hab.symm
        · exact hJind a ha b hb hab
      have := hJmax _ hins
      rw [card_insert_of_notMem hxJ] at this
      omega
  have hcard : #I ≤ Fintype.card V - G.maxDegree := by
    have h1 : #I = #J + 1 := card_insert_of_notMem hvJ
    have h2 : #J ≤ #R := card_le_card hJR
    have h3 : #R + 1 + G.degree v = Fintype.card V := by
      have hvc : v ∈ (G.neighborFinset v)ᶜ := by simp
      rw [card_erase_of_mem hvc, card_compl, card_neighborFinset_eq_degree]
      have := G.degree_lt_card_verts v
      omega
    omega
  exact (Nat.sInf_le (s := {k | ∃ S, IsDom G S ∧ IsIndep G S ∧ #S = k}) ⟨I, hD, hI, rfl⟩).trans
    hcard

/-- A nonempty set inducing minimum degree at least `d` gives `SW(H) ≥ 1 + d`. -/
lemma le_SW_of (H : SimpleGraph V) (X : Finset V) (hX : X.Nonempty) (d : ℕ)
    (hd : ∀ x ∈ X, d ≤ #(X.filter (H.Adj x))) : 1 + d ≤ SW H := by
  have hbdd : BddAbove {d | ∃ X : Finset V, X.Nonempty ∧ ∀ x ∈ X, d ≤ #(X.filter (H.Adj x))} := by
    refine ⟨Fintype.card V, ?_⟩
    rintro d ⟨X, ⟨x, hx⟩, hd⟩
    exact (hd x hx).trans ((card_filter_le _ _).trans (card_le_univ X))
  have := le_csSup hbdd ⟨X, hX, hd⟩
  unfold SW
  omega

/-- `SW(Ḡ) ≥ n - Δ(G)`. -/
lemma le_SW (G : SimpleGraph V) [Nonempty V] : Fintype.card V - G.maxDegree ≤ SW Gᶜ := by
  have h := le_SW_of Gᶜ univ univ_nonempty (Fintype.card V - 1 - G.maxDegree) fun x _ => by
    have hsub : (univ.erase x) \ G.neighborFinset x ⊆ univ.filter (Gᶜ.Adj x) := by
      intro y hy
      simp only [mem_sdiff, mem_erase, mem_univ, and_true, mem_neighborFinset] at hy
      simp only [mem_filter, mem_univ, true_and, compl_adj]
      exact ⟨Ne.symm hy.1, hy.2⟩
    have hN : G.neighborFinset x ⊆ univ.erase x := fun y hy =>
      mem_erase.mpr ⟨(G.ne_of_adj ((mem_neighborFinset _ _ _).mp hy)).symm, mem_univ y⟩
    have hc := card_le_card hsub
    rw [card_sdiff_of_subset hN, card_erase_of_mem (mem_univ x), card_univ,
      card_neighborFinset_eq_degree] at hc
    have := G.degree_le_maxDegree x
    have hlt := G.degree_lt_card_verts x
    refine le_trans ?_ (le_of_le_of_eq hc (by congr 1; ext y; simp))
    omega
  have hlt := G.maxDegree_lt_card_verts
  omega

/-- `i(G) ≤ SW(Ḡ)`. -/
theorem indepDomNum_le_SW (G : SimpleGraph V) [Nonempty V] : indepDomNum G ≤ SW Gᶜ :=
  (indepDomNum_le G).trans (le_SW G)

/-- **WOWII Conjecture 434b.** -/
theorem conjecture434b (G : SimpleGraph V) [Nonempty V] :
    indepDomNum G ≤ minDegIn G (maxDegSet G) + 1 + SW Gᶜ ∧
      (2 < G.diam → indepDomNum G ≤ minDegIn G (maxDegSet G) + SW Gᶜ) := by
  have := indepDomNum_le_SW G
  constructor
  · omega
  · intro _
    omega

/-- **WOWII Conjecture 434c.** -/
theorem conjecture434c (G : SimpleGraph V) [Nonempty V] :
    indepDomNum G ≤ minDegIn G (maxDegSet G)ᶜ + 1 + SW Gᶜ ∧
      (G.minDegree = 1 → indepDomNum G ≤ minDegIn G (maxDegSet G)ᶜ + SW Gᶜ) := by
  have := indepDomNum_le_SW G
  constructor
  · omega
  · intro _
    omega

end WOWII434
