import OpenProblem.WOWII326
import OpenProblem.WOWII378

/-!
# Written on the Wall II, Conjecture 320

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 320.** Let `G` be a simple connected graph with `n > 1`. If
> `maximum dist_even(v) = Tdist_min(G)`, then `G` is well totally dominated.

Here `dist_even(v)` is the number of vertices at even distance from `v` (including `v`),
`Tdist(v) = ∑_u d(v, u)` is the total distance of `v`, and `Tdist_min` is its minimum.

We prove the conjecture (`conjecture320`).

* Neighbours of `w` are at distance one and the other vertices at distance at least two, so
  `Tdist(w) ≥ 2(n - 1) - deg(w) ≥ n - 1`, with equality only for a universal vertex.
* Neighbours of `v` are at odd distance, so `dist_even(v) ≤ n - deg(v) ≤ n - 1`.

So the hypothesis forces a universal vertex `w` and a vertex `v` of degree one. The unique
neighbour `z` of `v` lies in every total dominating set. Since `z` is universal, `z` together with
any of its neighbours is a total dominating set. So every minimal total dominating set has exactly
two vertices.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII320

open SimpleGraph WOWII372 WOWII326

variable {V : Type*} [Fintype V]

/-- The number of vertices at even distance from `v` (including `v`). -/
def distEven (G : SimpleGraph V) (v : V) : ℕ := #(univ.filter fun u => Even (G.dist v u))

/-- The total distance of `v`. -/
def Tdist (G : SimpleGraph V) (v : V) : ℕ := ∑ u, G.dist v u

/-- The maximum of `dist_even`. -/
def maxDistEven (G : SimpleGraph V) : ℕ := univ.sup (distEven G)

/-- The minimum total distance. -/
def TdistMin (G : SimpleGraph V) : ℕ := sInf (Set.range (Tdist G))

/-- `Tdist(w) + deg(w) ≥ 2(n - 1)` in a connected graph. -/
lemma Tdist_add_degree {G : SimpleGraph V} (hG : G.Connected) (w : V) :
    2 * (Fintype.card V - 1) ≤ Tdist G w + G.degree w := by
  have hpt : ∀ u, (if u = w then 0 else if G.Adj w u then 1 else 2) ≤ G.dist w u := by
    intro u
    by_cases huw : u = w
    · simp [huw]
    · by_cases hadj : G.Adj w u
      · simp [huw, hadj, dist_eq_one_iff_adj.mpr hadj]
      · simp only [huw, hadj, ite_false]
        exact WOWII378.two_le_dist (hG.preconnected w u) (Ne.symm huw) hadj
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) => hpt u
  -- evaluate the left-hand sum
  have hcount : ∑ u, (if u = w then 0 else if G.Adj w u then 1 else 2) +
      G.degree w + 2 = 2 * Fintype.card V := by
    have h1 : ∑ u, (if u = w then 0 else if G.Adj w u then 1 else 2) =
        ∑ u, (2 * (if u = w then 0 else 1) - (if G.Adj w u then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases huw : u = w
      · subst huw; simp
      · by_cases hadj : G.Adj w u <;> simp [huw, hadj]
    have h2 : ∑ u, (if G.Adj w u then 1 else 0) = G.degree w := by
      rw [Finset.sum_boole, Nat.cast_id, ← card_neighborFinset_eq_degree]
      congr 1
      ext u
      simp
    have h3 : ∑ u, (if u = w then 0 else 1) + 1 = Fintype.card V := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_ne', card_erase_of_mem (mem_univ w), card_univ]
      have := Fintype.card_pos_iff.mpr ⟨w⟩
      omega
    have h4 : ∀ u, (if G.Adj w u then 1 else 0) ≤ 2 * (if u = w then 0 else 1) := by
      intro u
      by_cases huw : u = w
      · subst huw; simp
      · by_cases hadj : G.Adj w u <;> simp [huw, hadj]
    rw [h1]
    have h5 := Finset.sum_tsub_distrib (s := univ) (f := fun u => 2 * (if u = w then 0 else 1))
      (g := fun u => if G.Adj w u then 1 else 0) (fun u _ => h4 u)
    rw [h5, ← Finset.mul_sum, h2]
    have h6 : G.degree w ≤ 2 * ∑ u, (if u = w then 0 else 1) := by
      rw [← h2, Finset.mul_sum]
      exact Finset.sum_le_sum fun u _ => h4 u
    omega
  unfold Tdist
  have := Fintype.card_pos_iff.mpr ⟨w⟩
  omega

/-- `dist_even(v) + deg(v) ≤ n`. -/
lemma distEven_add_degree (G : SimpleGraph V) (v : V) :
    distEven G v + G.degree v ≤ Fintype.card V := by
  rw [distEven, ← card_neighborFinset_eq_degree, ← card_univ]
  rw [← card_union_of_disjoint]
  · exact card_le_univ _
  · rw [Finset.disjoint_left]
    intro u hu hu'
    have he := (mem_filter.mp hu).2
    have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hu'
    rw [dist_eq_one_iff_adj.mpr hadj] at he
    exact Nat.not_even_one he

/-- **WOWII Conjecture 320.** If `G` is connected with at least two vertices and
`maximum dist_even(v) = Tdist_min(G)`, then `G` is well totally dominated. -/
theorem conjecture320 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (h : maxDistEven G = TdistMin G) : WellTotallyDominated G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos : ∀ v, 1 ≤ G.degree v := fun v => hG.preconnected.degree_pos_of_nontrivial v
  -- `Tdist_min` is attained at some `w`, and `max dist_even` at some `v`
  obtain ⟨w, hw⟩ := Nat.sInf_mem (Set.range_nonempty (Tdist G))
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup univ univ_nonempty (distEven G)
  have hTw := Tdist_add_degree hG w
  have hEv := distEven_add_degree G v
  have hdw := G.degree_lt_card_verts w
  have hdv := hpos v
  have hmax : maxDistEven G = distEven G v := hv
  have hmin : TdistMin G = Tdist G w := hw.symm
  -- hence `w` is universal and `v` has degree one
  have hwuniv : G.degree w = Fintype.card V - 1 := by omega
  have hv1 : G.degree v = 1 := by omega
  have hwadj : ∀ u, u ≠ w → G.Adj w u := by
    intro u hu
    have hN : G.neighborFinset w = univ.erase w := by
      apply eq_of_subset_of_card_le
      · intro x hx
        exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset w x).mp hx)).symm, mem_univ x⟩
      · rw [card_erase_of_mem (mem_univ w), card_univ, card_neighborFinset_eq_degree, hwuniv]
    have : u ∈ G.neighborFinset w := by rw [hN]; exact mem_erase.mpr ⟨hu, mem_univ u⟩
    exact (G.mem_neighborFinset w u).mp this
  -- the unique neighbour `z` of `v` is universal
  obtain ⟨z, hvz⟩ := (G.degree_pos_iff_exists_adj v).mp (hpos v)
  have hzuniv : ∀ u, u ≠ z → G.Adj z u := by
    by_cases hvw : v = w
    · -- then `n = 2`
      subst hvw
      have hn2 : Fintype.card V = 2 := by omega
      intro u hu
      have huv : u = v := by
        by_contra huv
        have : #({u, v, z} : Finset V) ≤ Fintype.card V := card_le_univ _
        rw [card_insert_of_notMem (by simp [huv, hu]), card_pair (G.ne_of_adj hvz)] at this
        omega
      rw [huv]
      exact hvz.symm
    · have hzw : z = w :=
        WOWII377.eq_of_degree_le_one (le_of_eq hv1) hvz (hwadj v hvw).symm
      rw [hzw]
      exact hwadj
  -- every minimal total dominating set has two vertices
  have key : ∀ S, IsMinTDS G S → #S = 2 := by
    intro S ⟨hS, hmin⟩
    obtain ⟨z', hz'S, hvz'⟩ := hS v
    have hz' : z' = z := WOWII377.eq_of_degree_le_one (le_of_eq hv1) hvz' hvz
    subst hz'
    obtain ⟨u, huS, hzu⟩ := hS z'
    have hT : IsTDS G {z', u} := by
      intro t
      by_cases htz : t = z'
      · exact ⟨u, by simp, htz ▸ hzu⟩
      · exact ⟨z', by simp, (hzuniv t htz).symm⟩
    have hsub : ({z', u} : Finset V) ⊆ S := by
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact hz'S
      · rw [mem_singleton.mp ht]; exact huS
    have heq : S = {z', u} := by
      by_contra hne
      exact hmin _ (ssubset_of_subset_of_ne hsub (Ne.symm hne)) hT
    rw [heq, card_pair (G.ne_of_adj hzu)]
  intro S T hS hT
  rw [key S hS, key T hT]

end WOWII320
