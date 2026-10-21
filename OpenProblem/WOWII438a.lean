import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 438a

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 438a.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ a(G) + a(G[V - A]) + |E(G[A])|`, where `A` is the set of vertices of minimum degree.

Here `α_2` is the 2-independence number and `a` is the annihilation number: the largest `k` such
that the `k` smallest degrees sum to at most the number of edges. Equivalently, `a(G)` is the
largest size of a vertex set whose degrees sum to at most `|E(G)|`, which is how we define it
(`annihilation`). This agrees with formal-conjectures' `SimpleGraph.annihilationNumber`, which
maximises over sub-multisets of the degree multiset. For `G[V - A]` the degrees and the edges are
those of the induced subgraph (`annihilationIn`).

We prove the conjecture for every finite graph (`conjecture438a`).

* **Pepper's bound** `α ≤ a` (`card_le_annihilationIn`). If `S ⊆ X` is independent, the edges
  of `G[X]` at the vertices of `S` are distinct, so the degrees of `S` in `G[X]` sum to at most
  `|E(G[X])|`.
* **Splitting a 2-independent set.** A 2-independent set `J` induces a matching plus isolated
  vertices. Order the vertices so that those outside `A` come last, and call a vertex of `J`
  *upper* if its neighbour in `J` comes earlier.
  * The vertices of `J` that are not upper form an independent set, so there are at most `a(G)`
    of them.
  * The upper vertices outside `A` form an independent set of `G[V - A]`, so there are at most
    `a(G[V - A])` of them.
  * An upper vertex in `A` has its neighbour in `J` in `A` as well, by the choice of order. So
    these vertices give distinct edges of `G[A]`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII438a

open SimpleGraph WOWII449

variable {V : Type*} [Fintype V]

/-! ### Definitions -/

/-- The vertices of minimum degree. -/
def minDegSet (G : SimpleGraph V) : Finset V := univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

/-- The annihilation number `a(G)`: the largest size of a vertex set whose degrees sum to at most
the number of edges. -/
def annihilation (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ S : Finset V, #S = k ∧ ∑ v ∈ S, G.degree v ≤ #G.edgeFinset}

/-- The annihilation number of the induced subgraph `G[X]`, with the degrees and the edges of
`G[X]`. -/
def annihilationIn (G : SimpleGraph V) (X : Finset V) : ℕ :=
  sSup {k | ∃ S ⊆ X, #S = k ∧ ∑ v ∈ S, #(X.filter (G.Adj v)) ≤ edgesIn G X}

/-- The statement of Conjecture 438a. -/
def Conjecture438a : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    twoIndepNum G ≤
      annihilation G + annihilationIn G (univ \ minDegSet G) + edgesIn G (minDegSet G)

/-! ### Independent sets and the annihilation number -/

/-- The degrees in `G[X]` of an independent set `S ⊆ X` sum to at most `|E(G[X])|`. -/
lemma sum_degIn_le (G : SimpleGraph V) {X S : Finset V} (hSX : S ⊆ X)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    ∑ v ∈ S, #(X.filter (G.Adj v)) ≤ edgesIn G X := by
  rw [← card_sigma, edgesIn]
  refine card_le_card_of_injOn (s := S.sigma fun v => X.filter (G.Adj v))
    (t := G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ X) (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    simp only [mem_coe, mem_sigma, mem_filter] at hp
    simp only [mem_coe, mem_filter, mem_edgeFinset, mem_edgeSet]
    refine ⟨hp.2.2, fun u hu => ?_⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    exacts [hSX hp.1, hp.2.1]
  · intro p hp q hq hpq
    simp only [mem_coe, mem_sigma, mem_filter] at hp hq
    have hpq' : s(p.1, p.2) = s(q.1, q.2) := hpq
    rcases Sym2.eq_iff.mp hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Sigma.ext h1 (heq_of_eq h2)
    · exact absurd hp.2.2 (hS _ hp.1 _ (h2 ▸ hq.1))

/-- Pepper's bound for induced subgraphs: `α(G[X]) ≤ a(G[X])`. -/
lemma card_le_annihilationIn (G : SimpleGraph V) {X S : Finset V} (hSX : S ⊆ X)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) : #S ≤ annihilationIn G X :=
  le_csSup ⟨#X, fun _ ⟨_, hT, hk, _⟩ => hk ▸ card_le_card hT⟩
    ⟨S, hSX, rfl, sum_degIn_le G hSX hS⟩

/-- Pepper's bound: `α(G) ≤ a(G)`. -/
lemma card_le_annihilation (G : SimpleGraph V) {S : Finset V}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) : #S ≤ annihilation G := by
  have h := sum_degIn_le G (subset_univ S) hS
  have hdeg : ∀ v, #(univ.filter (G.Adj v)) = G.degree v := fun v => by
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have hE : edgesIn G univ = #G.edgeFinset := by
    rw [edgesIn, filter_true_of_mem fun e _ v _ => mem_univ v]
  simp only [hdeg, hE] at h
  exact le_csSup ⟨Fintype.card V, fun _ ⟨T, hk, _⟩ => hk ▸ card_le_univ T⟩ ⟨S, rfl, h⟩

/-! ### The main bound -/

/-- **WOWII Conjecture 438a**, for every finite graph. -/
theorem twoIndepNum_le (G : SimpleGraph V) :
    twoIndepNum G ≤
      annihilation G + annihilationIn G (univ \ minDegSet G) + edgesIn G (minDegSet G) := by
  obtain ⟨J, hJ, hcard⟩ := exists_twoIndep G
  rw [← hcard]
  set A := minDegSet G
  -- an order on the vertices with the vertices outside `A` last
  let κ : V → ℕ := fun v => (if v ∈ A then 0 else Fintype.card V) + (Fintype.equivFin V v : ℕ)
  have hlt : ∀ v, (Fintype.equivFin V v : ℕ) < Fintype.card V := fun v => (Fintype.equivFin V v).2
  have hκ : ∀ v w, κ v = κ w → v = w := by
    intro v w h
    have h1 := hlt v
    have h2 := hlt w
    have : (Fintype.equivFin V v : ℕ) = Fintype.equivFin V w := by
      simp only [κ] at h
      split_ifs at h <;> omega
    exact (Fintype.equivFin V).injective (Fin.ext this)
  have hκA : ∀ v w, v ∈ A → w ∉ A → κ v < κ w := by
    intro v w hv hw
    have := hlt v
    simp only [κ, hv, hw, ↓reduceIte]
    omega
  -- a vertex of `J` has at most one neighbour in `J`
  have huniq : ∀ v ∈ J, ∀ u ∈ J, ∀ w ∈ J, G.Adj v u → G.Adj v w → u = w := fun v hv u hu w hw
    hvu hvw => card_le_one.mp (hJ v hv) u (mem_filter.mpr ⟨hu, hvu⟩) w (mem_filter.mpr ⟨hw, hvw⟩)
  set J2 := J.filter fun v => ∃ w ∈ J, G.Adj v w ∧ κ w < κ v with hJ2
  set J1 := J.filter fun v => ¬ ∃ w ∈ J, G.Adj v w ∧ κ w < κ v with hJ1
  -- the vertices that are not upper
  have h1 : #J1 ≤ annihilation G := by
    refine card_le_annihilation G fun x hx y hy hxy => ?_
    simp only [hJ1, mem_filter] at hx hy
    rcases lt_or_gt_of_ne (fun h => hxy.ne (hκ x y h)) with h | h
    · exact hy.2 ⟨x, hx.1, hxy.symm, h⟩
    · exact hx.2 ⟨y, hy.1, hxy, h⟩
  -- the upper vertices form an independent set
  have hJ2ind : ∀ x ∈ J2, ∀ y ∈ J2, ¬ G.Adj x y := by
    intro x hx y hy hxy
    simp only [hJ2, mem_filter] at hx hy
    obtain ⟨w, hw, hxw, hwx⟩ := hx.2
    obtain ⟨w', hw', hyw', hw'y⟩ := hy.2
    rw [huniq x hx.1 w hw y hy.1 hxw hxy] at hwx
    rw [huniq y hy.1 w' hw' x hx.1 hyw' hxy.symm] at hw'y
    omega
  have h2 : #(J2.filter (· ∉ A)) ≤ annihilationIn G (univ \ A) := by
    refine card_le_annihilationIn G (fun v hv => ?_) fun x hx y hy =>
      hJ2ind x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
    simp only [mem_filter] at hv
    exact mem_sdiff.mpr ⟨mem_univ v, hv.2⟩
  -- the upper vertices in `A` give distinct edges of `G[A]`
  have h3 : #(J2.filter (· ∈ A)) ≤ edgesIn G A := by
    have hex : ∀ v ∈ J2, ∃ w ∈ J, G.Adj v w ∧ κ w < κ v := fun v hv => (mem_filter.mp hv).2
    choose! p hpJ hpadj hplt using hex
    refine card_le_card_of_injOn (fun v => s(v, p v)) (fun v hv => ?_)
      (fun v hv v' hv' hvv => ?_)
    · simp only [mem_coe, mem_filter] at hv
      have hpA : p v ∈ A := by
        by_contra hpA
        have := hκA v (p v) hv.2 hpA
        have := hplt v hv.1
        omega
      simp only [mem_coe, mem_filter, mem_edgeFinset, mem_edgeSet]
      refine ⟨hpadj v hv.1, fun u hu => ?_⟩
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      exacts [hv.2, hpA]
    · simp only [mem_coe, mem_filter] at hv hv'
      have hvv' : s(v, p v) = s(v', p v') := hvv
      rcases Sym2.eq_iff.mp hvv' with ⟨h, -⟩ | ⟨h, h'⟩
      · exact h
      · have h1 := hplt v hv.1
        have h2 := hplt v' hv'.1
        rw [h'] at h1
        rw [← h] at h2
        omega
  have hsplit1 := card_filter_add_card_filter_not (s := J)
    (fun v => ∃ w ∈ J, G.Adj v w ∧ κ w < κ v)
  have hsplit2 := card_filter_add_card_filter_not (s := J2) (· ∈ A)
  rw [← hJ2, ← hJ1] at hsplit1
  omega

/-- **WOWII Conjecture 438a.** -/
theorem conjecture438a : Conjecture438a := fun _ _ G _ _ => twoIndepNum_le G

end WOWII438a
