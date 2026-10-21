import OpenProblem.WOWII326

/-!
# Written on the Wall II, Conjecture 323

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 323.** Let `G` be a simple connected graph with `n > 1`. If
> `max {|N_Ḡ(e)| : e an edge of Ḡ} ≤ 1 + max {dist_odd(v) - odd horizontal(v) : v ∈ V(G)}`, then
> `G` is well totally dominated.

Here `N_Ḡ(uw) = N_Ḡ(u) ∪ N_Ḡ(w)`, `dist_odd(v)` is the number of vertices at odd distance from
`v`, and `odd horizontal(v)` is the number of edges whose endpoints are at the same odd distance
from `v` (as in formal-conjectures' Conjecture 309). `G` is *well totally dominated* if all
minimal total dominating sets have the same size.

We prove the conjecture (`conjecture323`): its hypothesis forces every minimal total dominating
set to have exactly two vertices. Let `v` attain the maximum, `A = N(v)` and `B = V - A`.

* **Diameter at most two.** If `d(x, y) ≥ 3`, then `N_Ḡ(x) ∪ N_Ḡ(y) = V`, so `dist_odd(v) = n - 1`.
  All other vertices are then at odd distance from `v`, so all are adjacent to `v`, which is a
  contradiction.
* So `dist_odd(v) ≤ deg v`, and `odd horizontal(v) ≥ |E(G[A])|`. For non-adjacent `u ≠ w`,
  `|N_Ḡ(u) ∪ N_Ḡ(w)| = n - |N(u) ∩ N(w)|`, so every non-adjacent pair has at least `n - L` common
  neighbours, where `L` is the left-hand side, and `|E(G[A])| ≤ 1 + |A| - L`.
* **`G` contains the complete bipartite graph between `A` and `B`.** If `b ∈ B - {v}` missed
  `a ∈ A`, their common neighbours would lie in `N_A(a) ∪ (B - {b, v})`, giving at most
  `|E(G[A])| + |B| - 2 < n - L` of them.
* **Minimal total dominating sets.** A set meeting both `A` and `B` contains a dominating pair
  `{a, b}`. No total dominating set lies inside `B`, since `v` has no neighbour there. A minimal
  set inside `A` contains an edge `xy`, and a vertex `z ∈ A` missing both `x` and `y` is ruled out
  by counting the edges of `G[A]` through `x`, `z` and their common neighbours.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII323

open WOWII372 WOWII326

variable {V : Type*} [Fintype V]

/-! ### Definitions -/

/-- The number of vertices at odd distance from `v`. -/
def distOdd (G : SimpleGraph V) (v : V) : ℕ := #(univ.filter fun u => Odd (G.dist v u))

/-- The number of edges whose endpoints are at the same odd distance from `v`. -/
def oddHorizontal (G : SimpleGraph V) (v : V) : ℕ :=
  #(G.edgeFinset.filter fun e => ∃ d, Odd d ∧ ∀ u ∈ e, G.dist v u = d)

/-- `|N_Ḡ(e)|`, the size of the union of the neighbourhoods in `Ḡ` of the ends of `e`. -/
def complNbr (G : SimpleGraph V) (e : Sym2 V) : ℕ := #(univ.filter fun x => ∃ u ∈ e, Gᶜ.Adj u x)

/-- `max {|N_Ḡ(e)| : e ∈ E(Ḡ)}` (zero if `Ḡ` has no edges). -/
def maxComplNbr (G : SimpleGraph V) : ℕ := Gᶜ.edgeFinset.sup (complNbr G)

/-- The number of edges of `G[A]`. -/
def edgesIn (G : SimpleGraph V) (A : Finset V) : ℕ := #(G.edgeFinset.filter fun e => ∀ u ∈ e, u ∈ A)

/-- The statement of Conjecture 323. Taking a maximum over `v` on the right-hand side is the same
as asking for one vertex `v`. -/
def Conjecture323 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 1 < Fintype.card V →
    (∃ v, (maxComplNbr G : ℤ) ≤ 1 + distOdd G v - oddHorizontal G v) → WellTotallyDominated G

/-! ### Lemmas -/

/-- For non-adjacent `u ≠ w`, `|N_Ḡ(u) ∪ N_Ḡ(w)| + |N(u) ∩ N(w)| = n`. -/
lemma complNbr_add_common (G : SimpleGraph V) {u w : V} (huw : u ≠ w) (hn : ¬ G.Adj u w) :
    complNbr G s(u, w) + #(univ.filter fun z => G.Adj u z ∧ G.Adj w z) = Fintype.card V := by
  have h : (univ.filter fun x => ∃ y ∈ s(u, w), Gᶜ.Adj y x) =
      univ.filter fun z => ¬ (G.Adj u z ∧ G.Adj w z) := by
    ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, hyz⟩ ⟨h3, h4⟩
      rw [Sym2.mem_iff] at hy
      rw [compl_adj] at hyz
      rcases hy with rfl | rfl
      · exact hyz.2 h3
      · exact hyz.2 h4
    · intro h
      by_cases hzu : z = u
      · subst hzu
        exact ⟨w, Sym2.mem_mk_right _ _, (compl_adj G w z).mpr ⟨Ne.symm huw, fun h' => hn h'.symm⟩⟩
      by_cases hzw : z = w
      · subst hzw
        exact ⟨u, Sym2.mem_mk_left _ _, (compl_adj G u z).mpr ⟨huw, hn⟩⟩
      by_cases hu : G.Adj u z
      · exact ⟨w, Sym2.mem_mk_right _ _, (compl_adj G w z).mpr ⟨Ne.symm hzw, fun h' => h ⟨hu, h'⟩⟩⟩
      · exact ⟨u, Sym2.mem_mk_left _ _, (compl_adj G u z).mpr ⟨Ne.symm hzu, hu⟩⟩
  rw [complNbr, h, add_comm]
  exact card_filter_add_card_filter_not _

/-- Every non-adjacent pair has at least `n - L` common neighbours. -/
lemma common_ge (G : SimpleGraph V) {u w : V} (huw : u ≠ w) (hn : ¬ G.Adj u w) :
    (Fintype.card V : ℤ) - maxComplNbr G ≤ #(univ.filter fun z => G.Adj u z ∧ G.Adj w z) := by
  have h1 := complNbr_add_common G huw hn
  have h2 : complNbr G s(u, w) ≤ maxComplNbr G :=
    le_sup (mem_edgeFinset.mpr ((compl_adj G u w).mpr ⟨huw, hn⟩))
  omega

omit [Fintype V] in
/-- A minimal total dominating set containing a dominating pair is that pair. -/
lemma card_eq_two {G : SimpleGraph V} {S : Finset V} (hS : IsMinTDS G S) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : x ≠ y) (h : IsTDS G {x, y}) : #S = 2 := by
  have hsub : ({x, y} : Finset V) ⊆ S := insert_subset hx (singleton_subset_iff.mpr hy)
  have heq : ({x, y} : Finset V) = S := by
    by_contra hne
    exact hS.2 _ (ssubset_of_subset_of_ne hsub hne) h
  rw [← heq, card_pair hxy]

/-- The hypothesis forces diameter at most two. -/
lemma dist_le_two (G : SimpleGraph V) (hG : G.Connected) (v : V)
    (hv : (maxComplNbr G : ℤ) ≤ 1 + distOdd G v - oddHorizontal G v) (x y : V) :
    G.dist x y ≤ 2 := by
  by_contra hxy
  push Not at hxy
  have hne : x ≠ y := by
    rintro rfl
    simp at hxy
  have hnadj : ¬ G.Adj x y := fun h => by
    rw [dist_eq_one_iff_adj.mpr h] at hxy
    omega
  have hnocommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z) := by
    rintro z ⟨h1, h2⟩
    have := hG.dist_triangle (u := x) (v := z) (w := y)
    rw [dist_eq_one_iff_adj.mpr h1, dist_eq_one_iff_adj.mpr h2.symm] at this
    omega
  have hcom := common_ge G hne hnadj
  have h0 : #(univ.filter fun z => G.Adj x z ∧ G.Adj y z) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro z _
    exact hnocommon z
  rw [h0] at hcom
  -- every vertex other than `v` is at odd distance from `v`
  have hall : ∀ u, u ≠ v → Odd (G.dist v u) := by
    by_contra h
    push Not at h
    obtain ⟨u, huv, hu⟩ := h
    have hsub : univ.filter (fun u => Odd (G.dist v u)) ⊆ (univ.erase v).erase u := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      simp only [mem_erase, mem_univ, and_true]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · subst h
        exact hu ht
      · subst h
        simp at ht
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_erase.mpr ⟨huv, mem_univ u⟩), card_erase_of_mem (mem_univ v),
      card_univ] at this
    have := Fintype.one_lt_card_iff.mpr ⟨x, y, hne⟩
    unfold distOdd at hv
    omega
  -- so every vertex is adjacent to `v`
  have hadj : ∀ u, u ≠ v → G.Adj v u := by
    intro u huv
    by_contra hna
    have hodd := hall u huv
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v u
    have h1 : G.dist v u ≠ 1 := fun h => hna (dist_eq_one_iff_adj.mp h)
    have hge : 3 ≤ p.length := by
      obtain ⟨k, hk⟩ := hodd
      omega
    cases p with
    | nil => simp at hge
    | cons h1' p' =>
      cases p' with
      | nil => simp at hge
      | cons h2' q =>
        rename_i a b
        have hle2 : G.dist v b ≤ 2 := by
          have := dist_le (Walk.cons h1' (Walk.cons h2' Walk.nil))
          simpa using this
        have htri := hG.dist_triangle (u := v) (v := b) (w := u)
        have hq := dist_le q
        simp only [Walk.length_cons] at hp
        have hb2 : G.dist v b = 2 := by omega
        have hbv : b ≠ v := by
          rintro rfl
          simp at hb2
        have := hall b hbv
        rw [hb2] at this
        exact absurd this (by decide)
  -- then `x` and `y` are at distance at most two
  by_cases hxv : x = v
  · subst hxv
    rw [dist_eq_one_iff_adj.mpr (hadj y (Ne.symm hne))] at hxy
    omega
  by_cases hyv : y = v
  · subst hyv
    rw [dist_eq_one_iff_adj.mpr (hadj x hne).symm] at hxy
    omega
  exact hnocommon v ⟨(hadj x hxv).symm, (hadj y hyv).symm⟩

/-- `A`-neighbours of a vertex of `A` give distinct edges of `G[A]`. -/
lemma card_filter_adj_le (G : SimpleGraph V) (A : Finset V) {a : V} (ha : a ∈ A) :
    #(A.filter (G.Adj a)) ≤ edgesIn G A := by
  refine card_le_card_of_injOn (fun w => s(a, w)) (fun w hw => ?_) (fun w1 _ w2 _ h => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq] at hw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_edgeFinset, mem_edgeSet]
    refine ⟨hw.2, fun u hu => ?_⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact ha
    · exact hw.1
  · exact Sym2.congr_right.mp h

/-! ### The conjecture -/

/-- **WOWII Conjecture 323.** Under its hypothesis every minimal total dominating set has exactly
two vertices. -/
theorem conjecture323 : Conjecture323 := by
  intro V _ G hG _ ⟨v, hv⟩
  have hdist := dist_le_two G hG v hv
  set n := Fintype.card V
  set L := maxComplNbr G
  set A := G.neighborFinset v with hA
  have hmemA : ∀ u, u ∈ A ↔ G.Adj v u := fun u => mem_neighborFinset G v u
  have hvA : v ∉ A := by simp [hmemA]
  -- `dist_odd(v) ≤ deg v` and `odd horizontal(v) ≥ |E(G[A])|`
  have hodd : distOdd G v ≤ #A := by
    refine card_le_card fun u hu => ?_
    simp only [mem_filter, mem_univ, true_and] at hu
    rw [hmemA, ← dist_eq_one_iff_adj]
    have := hdist v u
    obtain ⟨k, hk⟩ := hu
    omega
  have hhor : edgesIn G A ≤ oddHorizontal G v := by
    refine card_le_card fun e he => ?_
    simp only [mem_filter] at he
    simp only [mem_filter]
    refine ⟨he.1, 1, odd_one, fun u hu => ?_⟩
    rw [dist_eq_one_iff_adj]
    exact (hmemA u).mp (he.2 u hu)
  have hkey : (edgesIn G A : ℤ) ≤ 1 + #A - L := by omega
  have hAc : #Aᶜ = n - #A := card_compl A
  have hAn : #A ≤ n := card_le_univ A
  -- every vertex of `B - {v}` is adjacent to all of `A`
  have hstep : ∀ b, b ∉ A → b ≠ v → ∀ a ∈ A, G.Adj b a := by
    intro b hb hbv a ha
    by_contra hba
    have hne : b ≠ a := by
      rintro rfl
      exact hb ha
    have hcom := common_ge G hne hba
    have hsub : univ.filter (fun z => G.Adj b z ∧ G.Adj a z) ⊆
        A.filter (G.Adj a) ∪ (Aᶜ.erase b).erase v := by
      intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      by_cases hzA : z ∈ A
      · exact mem_union_left _ (mem_filter.mpr ⟨hzA, hz.2⟩)
      · refine mem_union_right _ ?_
        simp only [mem_erase, mem_compl]
        refine ⟨fun h => ?_, (G.ne_of_adj hz.1).symm, hzA⟩
        subst h
        exact hb ((hmemA b).mpr hz.1.symm)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_filter_adj_le G A ha
    have h3 : #((Aᶜ.erase b).erase v) = #Aᶜ - 2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hbv, mem_compl.mpr hvA⟩),
        card_erase_of_mem (mem_compl.mpr hb)]
      omega
    have h4 : 2 ≤ #Aᶜ := by
      have : ({b, v} : Finset V) ⊆ Aᶜ := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_compl.mpr hb
        · exact mem_compl.mpr hvA
      have := card_le_card this
      rwa [card_pair hbv] at this
    omega
  -- every vertex outside `A` is adjacent to all of `A`
  have hout : ∀ z, z ∉ A → ∀ a ∈ A, G.Adj z a := by
    intro z hz a ha
    by_cases hzv : z = v
    · subst hzv
      exact (hmemA a).mp ha
    · exact hstep z hz hzv a ha
  -- every minimal total dominating set has two vertices
  have htwo : ∀ S, IsMinTDS G S → #S = 2 := by
    intro S hS
    obtain ⟨u, huS, hvu⟩ := hS.1 v
    have huA : u ∈ A := (hmemA u).mpr hvu
    by_cases hmix : ∃ b ∈ S, b ∉ A
    · obtain ⟨b, hbS, hbA⟩ := hmix
      refine card_eq_two hS huS hbS (fun h => hbA (h ▸ huA)) fun z => ?_
      by_cases hzA : z ∈ A
      · exact ⟨b, by simp, (hout b hbA z hzA).symm⟩
      · exact ⟨u, by simp, hout z hzA u huA⟩
    push Not at hmix
    obtain ⟨y, hyS, hxy⟩ := hS.1 u
    have hyA : y ∈ A := hmix y hyS
    refine card_eq_two hS huS hyS (G.ne_of_adj hxy) fun z => ?_
    by_cases hzA : z ∉ A
    · exact ⟨u, by simp, hout z hzA u huA⟩
    push Not at hzA
    by_cases hzu : z = u
    · exact ⟨y, by simp, hzu ▸ hxy⟩
    by_cases hzy : z = y
    · exact ⟨u, by simp, hzy ▸ hxy.symm⟩
    by_contra hno
    have hzx : ¬ G.Adj z u := fun h => hno ⟨u, by simp, h⟩
    have hzy' : ¬ G.Adj z y := fun h => hno ⟨y, by simp, h⟩
    -- the common `A`-neighbours of `z` and `u`
    set K := A.filter fun w => G.Adj z w ∧ G.Adj u w with hK
    have hcom := common_ge G hzu hzx
    have hsub : univ.filter (fun w => G.Adj z w ∧ G.Adj u w) ⊆ K ∪ Aᶜ := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      by_cases hwA : w ∈ A
      · exact mem_union_left _ (by simp [hK, hwA, hw])
      · exact mem_union_right _ (mem_compl.mpr hwA)
    have hc1 := (card_le_card hsub).trans (card_union_le _ _)
    -- edges of `G[A]` through `u`, `y`, `z` and `K`
    have hT : insert s(u, y) (K.image (fun w => s(z, w)) ∪ K.image (fun w => s(u, w))) ⊆
        G.edgeFinset.filter fun e => ∀ t ∈ e, t ∈ A := by
      intro e he
      simp only [mem_insert, mem_union, mem_image] at he
      simp only [mem_filter, mem_edgeFinset]
      rcases he with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
      · refine ⟨hxy, fun t ht => ?_⟩
        rcases Sym2.mem_iff.mp ht with rfl | rfl
        · exact huA
        · exact hyA
      · simp only [hK, mem_filter] at hw
        refine ⟨hw.2.1, fun t ht => ?_⟩
        rcases Sym2.mem_iff.mp ht with rfl | rfl
        · exact hzA
        · exact hw.1
      · simp only [hK, mem_filter] at hw
        refine ⟨hw.2.2, fun t ht => ?_⟩
        rcases Sym2.mem_iff.mp ht with rfl | rfl
        · exact huA
        · exact hw.1
    have hTcard : #(insert s(u, y) (K.image (fun w => s(z, w)) ∪ K.image (fun w => s(u, w)))) =
        1 + 2 * #K := by
      have hinj1 : Set.InjOn (fun w => s(z, w)) K := fun w1 _ w2 _ h => Sym2.congr_right.mp h
      have hinj2 : Set.InjOn (fun w => s(u, w)) K := fun w1 _ w2 _ h => Sym2.congr_right.mp h
      have hdisj : Disjoint (K.image (fun w => s(z, w))) (K.image (fun w => s(u, w))) := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [mem_image] at he1 he2
        obtain ⟨w1, hw1, rfl⟩ := he1
        obtain ⟨w2, hw2, h⟩ := he2
        simp only [hK, mem_filter] at hw1 hw2
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact hzu h1.symm
        · rw [h1] at hw2
          exact G.irrefl hw2.2.1
      have hnot : s(u, y) ∉ K.image (fun w => s(z, w)) ∪ K.image (fun w => s(u, w)) := by
        simp only [mem_union, mem_image, not_or, not_exists, not_and]
        refine ⟨fun w _ h => ?_, fun w hw h => ?_⟩
        · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hzu h1
          · exact hzy h1
        · simp only [hK, mem_filter] at hw
          rcases Sym2.eq_iff.mp h with ⟨-, h1⟩ | ⟨h1, -⟩
          · rw [h1] at hw
            exact hzy' hw.2.1
          · rw [← h1] at hxy
            exact G.irrefl hxy
      rw [card_insert_of_notMem hnot, card_union_of_disjoint hdisj, card_image_of_injOn hinj1,
        card_image_of_injOn hinj2]
      omega
    have hI1 := card_le_card hT
    rw [hTcard] at hI1
    -- `z` has a neighbour in `S ⊆ A`, giving a second edge of `G[A]`
    obtain ⟨t, htS, hzt⟩ := hS.1 z
    have htA : t ∈ A := hmix t htS
    have hI2 : ({s(u, y), s(z, t)} : Finset (Sym2 V)) ⊆
        G.edgeFinset.filter fun e => ∀ t ∈ e, t ∈ A := by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      simp only [mem_filter, mem_edgeFinset]
      rcases he with rfl | rfl
      · refine ⟨hxy, fun t ht => ?_⟩
        rcases Sym2.mem_iff.mp ht with rfl | rfl
        · exact huA
        · exact hyA
      · refine ⟨hzt, fun t' ht => ?_⟩
        rcases Sym2.mem_iff.mp ht with rfl | rfl
        · exact hzA
        · exact htA
    have hne2 : s(u, y) ≠ s(z, t) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact hzu h1.symm
      · exact hzy h1.symm
    have hI2' := card_le_card hI2
    rw [card_pair hne2] at hI2'
    have : (edgesIn G A : ℤ) = #(G.edgeFinset.filter fun e => ∀ t ∈ e, t ∈ A) := rfl
    omega
  intro S T hS hT
  rw [htwo S hS, htwo T hT]

end WOWII323
