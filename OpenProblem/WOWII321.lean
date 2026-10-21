import OpenProblem.WOWII323

/-!
# Written on the Wall II, Conjecture 321

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 321.** Let `G` be a simple connected graph with `n > 1`. If
> `ecc_avg(G) ≥ (1/3) Tdist_max(G)`, then `G` is well totally dominated.

Here `ecc_avg` is the average eccentricity and `Tdist(v) = Σ_u d(v, u)` is the total distance of
`v`. A graph is *well totally dominated* if all its minimal total dominating sets have the same
size.

We prove the conjecture (`conjecture321`).

* **At most six vertices** (`card_le_six`). Let `x, y` be at distance `D`, the diameter. Summing
  `d(x, v) + d(v, y) ≥ D` over all `v` gives `Tdist(x) + Tdist(y) ≥ nD`. The hypothesis gives
  `n Tdist(x) ≤ 3 Σ ecc ≤ 3nD`, so `Tdist(x), Tdist(y) ≤ 3D` and `n ≤ 6`.
* **Six vertices** (`wtd_six`). Every inequality above is now tight (`six_struct`). Every vertex
  `x` has eccentricity `D`, and an antipode `y` with `Tdist(x) = 3D`, and every vertex lies on a
  shortest path from `x` to `y`. So the four other vertices have distances from `x` in
  `[1, D - 1]`, summing to `2D`.
  * `D = 1` is impossible.
  * If `D = 2`, every vertex has exactly one non-neighbour, so the graph is `K_{2,2,2}`. Every
    edge is then a total dominating set, so every minimal one has two vertices
    (`wtd_of_one_nonnbr`).
  * If `D = 3`, every vertex has degree two, so the graph is `C_6`. Counting private neighbours
    shows that every minimal total dominating set has four vertices
    (`card_minTDS_two_regular`).
  * `D ≥ 4` is impossible. Take a vertex `x` with two neighbours `p, q`, and on a shortest path
    to its antipode the vertices `r, s` at distances `D - 1` and `D - 2`. These are the four
    other vertices, and their distances from `x` sum to `2D - 1`.
* **Two to five vertices** (`wtd_small`). We encode such graphs by numbers, and the kernel runs a
  checker (`check`) on every code (`check_two` to `check_five`, by `decide +kernel`). The checker
  computes distances by breadth-first search on bit masks and enumerates all vertex sets. Its
  correctness is proved (`connB_true`, `hypB_true` and `wtd_of_wtdB`), so the proof uses only
  the standard axioms.

Up to isomorphism, the graphs satisfying the hypothesis are `K_2`, `P_3`, `K_3`, `K_{1,3}`,
`P_4`, the paw, `C_4`, `K_4 - e`, `K_4`, `K_{2,3}`, `C_5`, the house, `K_{2,3}` plus an edge,
`K_{1,2,2}`, `C_6` and `K_{2,2,2}` (`wowii/experiments/c321.py`).
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII321

open WOWII326 WOWII372 WOWII323

variable {V : Type*} [Fintype V]

/-! ### Definitions -/

/-- The eccentricity of `v`: the largest distance from `v`. -/
def ecc (G : SimpleGraph V) (v : V) : ℕ := univ.sup fun w => G.dist v w

/-- The total distance (transmission) of `v`. -/
def Tdist (G : SimpleGraph V) (v : V) : ℕ := ∑ u, G.dist v u

/-- The largest total distance. -/
def TdistMax (G : SimpleGraph V) : ℕ := univ.sup (Tdist G)

/-- The average eccentricity. -/
def eccAvg (G : SimpleGraph V) : ℚ := (∑ v, (ecc G v : ℚ)) / Fintype.card V

/-- The statement of Conjecture 321. -/
def Conjecture321 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 1 < Fintype.card V →
    (TdistMax G : ℚ) / 3 ≤ eccAvg G → WellTotallyDominated G

/-! ### The hypothesis in natural numbers -/

lemma hyp_nat {G : SimpleGraph V} (hn : 0 < Fintype.card V)
    (h : (TdistMax G : ℚ) / 3 ≤ eccAvg G) (w : V) :
    Fintype.card V * Tdist G w ≤ 3 * ∑ v, ecc G v := by
  have h1 : Tdist G w ≤ TdistMax G := le_sup (f := Tdist G) (mem_univ w)
  have hn' : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  unfold eccAvg at h
  rw [div_le_div_iff₀ (by norm_num) hn'] at h
  have h2 : ((Fintype.card V * Tdist G w : ℕ) : ℚ) ≤ ((3 * ∑ v, ecc G v : ℕ) : ℚ) := by
    push_cast
    calc (Fintype.card V : ℚ) * Tdist G w ≤ Fintype.card V * TdistMax G := by
          gcongr
      _ = TdistMax G * Fintype.card V := by ring
      _ ≤ (∑ v, (ecc G v : ℚ)) * 3 := h
      _ = 3 * ∑ v, (ecc G v : ℚ) := by ring
  exact_mod_cast h2

/-! ### Distances -/

lemma dist_le_ecc (G : SimpleGraph V) (v w : V) : G.dist v w ≤ ecc G v :=
  le_sup (f := fun w => G.dist v w) (mem_univ w)

lemma exists_dist_eq_ecc (G : SimpleGraph V) [Nonempty V] (v : V) : ∃ w, G.dist v w = ecc G v := by
  obtain ⟨w, -, hw⟩ := exists_mem_eq_sup univ univ_nonempty (fun w => G.dist v w)
  exact ⟨w, hw.symm⟩

/-- Summing the triangle inequality over all vertices. -/
lemma card_mul_dist_le {G : SimpleGraph V} (hG : G.Connected) (x y : V) :
    Fintype.card V * G.dist x y ≤ Tdist G x + Tdist G y := by
  have : ∑ _v : V, G.dist x y ≤ ∑ v, (G.dist x v + G.dist y v) :=
    sum_le_sum fun v _ => by rw [G.dist_comm (u := y)]; exact hG.dist_triangle
  simpa [Tdist, sum_add_distrib] using this

omit [Fintype V] in
/-- The vertex before `v` on a shortest path from `x`. -/
lemma exists_pred {G : SimpleGraph V} (hG : G.Connected) {x v : V} {k : ℕ}
    (h : G.dist x v = k + 1) : ∃ w, G.Adj w v ∧ G.dist x w = k := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x v
  have hne : v ≠ x := by rintro rfl; simp at h
  obtain ⟨w, hvw, q, hq⟩ := Walk.exists_eq_cons_of_ne hne p.reverse
  have hl : p.length = q.length + 1 := by
    rw [← Walk.length_reverse p, hq, Walk.length_cons]
  refine ⟨w, hvw.symm, le_antisymm ?_ ?_⟩
  · calc G.dist x w = G.dist w x := G.dist_comm
      _ ≤ q.length := dist_le q
      _ = k := by omega
  · have := hG.dist_triangle (u := x) (v := w) (w := v)
    rw [dist_eq_one_iff_adj.mpr hvw.symm] at this
    omega

/-! ### At most six vertices -/

/-- The diameter. -/
def diam (G : SimpleGraph V) : ℕ := univ.sup (ecc G)

lemma ecc_le_diam (G : SimpleGraph V) (v : V) : ecc G v ≤ diam G := le_sup (f := ecc G) (mem_univ v)

lemma exists_diam_pair (G : SimpleGraph V) [Nonempty V] : ∃ x y, G.dist x y = diam G := by
  obtain ⟨x, -, hx⟩ := exists_mem_eq_sup univ univ_nonempty (ecc G)
  obtain ⟨y, hy⟩ := exists_dist_eq_ecc G x
  exact ⟨x, y, by rw [hy, diam, hx]⟩

lemma one_le_diam {G : SimpleGraph V} (hG : G.Connected) (hn : 1 < Fintype.card V) :
    1 ≤ diam G := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hn
  exact (hG.pos_dist_of_ne hab).trans_le ((dist_le_ecc G a b).trans (ecc_le_diam G a))

lemma sum_ecc_le (G : SimpleGraph V) : ∑ v, ecc G v ≤ Fintype.card V * diam G := by
  simpa using sum_le_sum fun v (_ : v ∈ univ) => ecc_le_diam G v

theorem card_le_six {G : SimpleGraph V} (hG : G.Connected) (hn : 1 < Fintype.card V)
    (hyp : ∀ w, Fintype.card V * Tdist G w ≤ 3 * ∑ v, ecc G v) : Fintype.card V ≤ 6 := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_diam_pair G
  have h1 := card_mul_dist_le hG x y
  have h2 := hyp x
  have h3 := hyp y
  have h4 := sum_ecc_le G
  have hD := one_le_diam hG hn
  rw [hxy] at h1
  set n := Fintype.card V
  set D := diam G
  have : n * (n * D) ≤ n * (6 * D) := by nlinarith
  have : n * D ≤ 6 * D := Nat.le_of_mul_le_mul_left this (by omega)
  exact Nat.le_of_mul_le_mul_right this (by omega)

/-! ### Six vertices -/

theorem six_struct {G : SimpleGraph V} (hG : G.Connected) (hn : Fintype.card V = 6)
    (hyp : ∀ w, Fintype.card V * Tdist G w ≤ 3 * ∑ v, ecc G v) :
    1 ≤ diam G ∧ ∀ x, ∃ y, G.dist x y = diam G ∧ Tdist G x = 3 * diam G ∧
      ∀ v, G.dist x v + G.dist v y = diam G := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hD := one_le_diam hG (by omega)
  refine ⟨hD, ?_⟩
  obtain ⟨x0, y0, hxy0⟩ := exists_diam_pair G
  have h4 := sum_ecc_le G
  have hS : ∑ v, ecc G v = 6 * diam G := by
    have h1 := card_mul_dist_le hG x0 y0
    have h2 := hyp x0
    have h3 := hyp y0
    rw [hxy0, hn] at h1
    rw [hn] at h2 h3 h4
    omega
  have hecc : ∀ v, ecc G v = diam G := by
    intro v
    by_contra hne
    have hlt : ecc G v < diam G := lt_of_le_of_ne (ecc_le_diam G v) hne
    have : ∑ w, ecc G w < ∑ _w : V, diam G :=
      sum_lt_sum (fun w _ => ecc_le_diam G w) ⟨v, mem_univ v, hlt⟩
    simp [hn] at this
    omega
  intro x
  obtain ⟨y, hy⟩ := exists_dist_eq_ecc G x
  rw [hecc x] at hy
  have h1 := card_mul_dist_le hG x y
  have h2 := hyp x
  have h3 := hyp y
  rw [hy, hn] at h1
  rw [hn, hS] at h2 h3
  refine ⟨y, hy, by omega, ?_⟩
  have hsum : ∑ v, (G.dist x v + G.dist v y) = ∑ _v : V, diam G := by
    have : ∑ v, (G.dist x v + G.dist v y) = Tdist G x + Tdist G y := by
      simp only [Tdist, sum_add_distrib]
      congr 1
      exact sum_congr rfl fun v _ => G.dist_comm
    rw [this]
    simp [hn]
    omega
  have := (sum_eq_sum_iff_of_le (s := univ) (f := fun _ => diam G)
    (g := fun v => G.dist x v + G.dist v y) fun v _ => by
      rw [← hy]; exact hG.dist_triangle).mp hsum.symm
  exact fun v => (this v (mem_univ v)).symm

/-! ### Well total domination in two special cases -/

omit [Fintype V] in
/-- If every vertex has at most one non-neighbour, every edge is a total dominating set, so every
minimal total dominating set has two vertices. -/
theorem wtd_of_one_nonnbr {G : SimpleGraph V} [Nonempty V]
    (h : ∀ z, ∃ y, ∀ v, v ≠ z → v ≠ y → G.Adj z v) : WellTotallyDominated G := by
  have hpair : ∀ a b, G.Adj a b → IsTDS G {a, b} := by
    intro a b hab z
    by_cases hza : z = a
    · subst hza; exact ⟨b, by simp, hab⟩
    by_cases hzb : z = b
    · subst hzb; exact ⟨a, by simp, hab.symm⟩
    obtain ⟨y, hy⟩ := h z
    by_cases hay : a = y
    · subst hay
      exact ⟨b, by simp, hy b (Ne.symm hzb) hab.ne.symm⟩
    · exact ⟨a, by simp, hy a (Ne.symm hza) hay⟩
  have h2 : ∀ S, IsMinTDS G S → #S = 2 := by
    intro S hS
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨a, ha, -⟩ := hS.1 v
    obtain ⟨b, hb, hab⟩ := hS.1 a
    exact card_eq_two hS ha hb hab.ne (hpair a b hab)
  intro S T hS hT
  rw [h2 S hS, h2 T hT]

omit [Fintype V] in
lemma card_filter_three {G : SimpleGraph V} {a b c : V} (hbc : b ≠ c) :
    #(({a, b, c} : Finset V).filter (G.Adj a)) =
      (if G.Adj a b then 1 else 0) + (if G.Adj a c then 1 else 0) := by
  rw [filter_insert, filter_insert, filter_singleton]
  simp only [SimpleGraph.irrefl, ↓reduceIte]
  split_ifs <;> simp [hbc]

/-- In a `2`-regular graph on six vertices every minimal total dominating set has four
vertices. -/
theorem card_minTDS_two_regular {G : SimpleGraph V} (hn : Fintype.card V = 6)
    (hdeg : ∀ x, #(univ.filter (G.Adj x)) = 2) {S : Finset V} (hS : IsMinTDS G S) :
    #S = 4 := by
  set f : V → ℕ := fun v => #(S.filter (G.Adj v)) with hf
  have h1 : ∀ v, 1 ≤ f v := fun v => by
    obtain ⟨u, hu, huv⟩ := hS.1 v
    exact card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, huv⟩⟩
  have h2 : ∀ v, f v ≤ 2 := fun v => by
    rw [← hdeg v]
    exact card_le_card fun u hu => by
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact hu.2
  have hsum : ∑ v, f v = 2 * #S := by
    simp only [hf, card_filter]
    rw [sum_comm, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s _ => ?_
    rw [← card_filter, ← hdeg s]
    congr 1
    ext v
    simp [G.adj_comm]
  have hpriv : ∀ s ∈ S, ∃ v, S.filter (G.Adj v) = {s} := by
    intro s hs
    have hnot := hS.2 (S.erase s) (erase_ssubset hs)
    unfold IsTDS at hnot
    push Not at hnot
    obtain ⟨v, hv⟩ := hnot
    refine ⟨v, ?_⟩
    ext u
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hu, huv⟩
      by_contra hne
      exact hv u (mem_erase.mpr ⟨hne, hu⟩) huv
    · rintro rfl
      obtain ⟨w, hw, hvw⟩ := hS.1 v
      by_cases hws : w = u
      · subst hws; exact ⟨hw, hvw⟩
      · exact absurd hvw (hv w (mem_erase.mpr ⟨hws, hw⟩))
  set P := univ.filter fun v => f v = 1 with hP
  have hSP : #S ≤ #P := by
    choose! g hg using hpriv
    refine card_le_card_of_injOn g (fun s hs => ?_) (fun s hs t ht hst => ?_)
    · simp [hP, hf, hg s hs]
    · have h' := hg s hs
      rw [show g s = g t from hst, hg t ht] at h'
      exact (singleton_inj.mp h').symm
  have hsplit : ∑ v, f v = #P + 2 * (6 - #P) := by
    rw [← sum_filter_add_sum_filter_not univ (fun v => f v = 1)]
    have hA : ∑ v ∈ univ.filter (fun v => f v = 1), f v = #P := by
      rw [card_eq_sum_ones]
      exact sum_congr rfl fun v hv => (mem_filter.mp hv).2
    have hB : ∑ v ∈ univ.filter (fun v => ¬ f v = 1), f v = 2 * (6 - #P) := by
      rw [sum_congr rfl (g := fun _ => 2) fun v hv => by
        have := h1 v; have := h2 v; have := (mem_filter.mp hv).2; omega]
      rw [sum_const, smul_eq_mul, filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ,
        hn]
      ring
    rw [hA, hB]
  have hP6 : #P ≤ 6 := hn ▸ card_le_univ P
  have hge : 6 ≤ ∑ v, f v := by
    have := sum_le_sum fun v (_ : v ∈ univ) => h1 v
    simpa [hn] using this
  rcases (by omega : #S = 3 ∨ #S = 4) with h3 | h4
  · exfalso
    have hP6' : P = univ := eq_univ_of_card P (by omega)
    have hall : ∀ v, f v = 1 := fun v => by
      have : v ∈ P := hP6' ▸ mem_univ v
      exact (mem_filter.mp this).2
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp h3
    have ha := hall a
    have hb := hall b
    have hc := hall c
    simp only [hf] at ha hb hc
    rw [card_filter_three hbc] at ha
    rw [show ({a, b, c} : Finset V) = {b, a, c} from insert_comm _ _ _,
      card_filter_three hac] at hb
    rw [show ({a, b, c} : Finset V) = {c, a, b} by ext; simp; tauto,
      card_filter_three hab] at hc
    rw [G.adj_comm b a] at hb
    rw [G.adj_comm c a, G.adj_comm c b] at hc
    split_ifs at ha hb hc <;> omega
  · exact h4

/-! ### The case of six vertices -/

theorem wtd_six {G : SimpleGraph V} (hG : G.Connected) (hn : Fintype.card V = 6)
    (hyp : ∀ w, Fintype.card V * Tdist G w ≤ 3 * ∑ v, ecc G v) : WellTotallyDominated G := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hD, hstr⟩ := six_struct hG hn hyp
  set D := diam G with hDdef
  -- the four vertices other than `x` and an antipode `y`
  have hW : ∀ x y, G.dist x y = D → Tdist G x = 3 * D → (∀ v, G.dist x v + G.dist v y = D) →
      x ≠ y ∧ #((univ.erase x).erase y) = 4 ∧
      ∑ v ∈ (univ.erase x).erase y, G.dist x v = 2 * D ∧
      ∀ v ∈ (univ.erase x).erase y, 1 ≤ G.dist x v ∧ G.dist x v + 1 ≤ D := by
    intro x y hxy hT hgeo
    have hne : x ≠ y := by rintro rfl; simp at hxy; omega
    have hy : y ∈ univ.erase x := mem_erase.mpr ⟨hne.symm, mem_univ y⟩
    refine ⟨hne, ?_, ?_, ?_⟩
    · rw [card_erase_of_mem hy, card_erase_of_mem (mem_univ x), card_univ, hn]
    · have h1 := add_sum_erase univ (fun v => G.dist x v) (mem_univ x)
      have h2 := add_sum_erase (univ.erase x) (fun v => G.dist x v) hy
      simp only [Tdist] at hT
      simp only [dist_self, zero_add] at h1
      rw [← h1, ← h2, hxy] at hT
      omega
    · intro v hv
      simp only [mem_erase] at hv
      have h1 := hG.pos_dist_of_ne hv.2.1.symm
      have h2 := hG.pos_dist_of_ne hv.1
      have := hgeo v
      omega
  rcases (by omega : D = 1 ∨ D = 2 ∨ D = 3 ∨ 4 ≤ D) with h | h | h | h
  · -- diameter one is impossible
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨y, hxy, hT, hgeo⟩ := hstr x
    obtain ⟨-, hc, -, hb⟩ := hW x y hxy hT hgeo
    obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < #((univ.erase x).erase y))
    have := hb v hv
    omega
  · -- diameter two: every vertex has one non-neighbour
    refine wtd_of_one_nonnbr fun z => ?_
    obtain ⟨y, hzy, hT, hgeo⟩ := hstr z
    obtain ⟨-, -, -, hb⟩ := hW z y hzy hT hgeo
    refine ⟨y, fun v hvz hvy => ?_⟩
    have := hb v (by simp [hvz, hvy])
    exact dist_eq_one_iff_adj.mp (by omega)
  · -- diameter three: the graph is `2`-regular
    have hdeg : ∀ x, #(univ.filter (G.Adj x)) = 2 := by
      intro x
      obtain ⟨y, hxy, hT, hgeo⟩ := hstr x
      obtain ⟨hne, hc, hs, hb⟩ := hW x y hxy hT hgeo
      set W := (univ.erase x).erase y
      have hF : univ.filter (G.Adj x) = W.filter fun v => G.dist x v = 1 := by
        ext v
        simp only [mem_filter, mem_univ, true_and]
        rw [← dist_eq_one_iff_adj]
        constructor
        · intro h1
          refine ⟨mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, mem_univ v⟩⟩, h1⟩
          · rintro rfl; rw [hxy] at h1; omega
          · rintro rfl; simp at h1
        · exact fun h1 => h1.2
      rw [hF]
      have hsplit := sum_filter_add_sum_filter_not W (fun v => G.dist x v = 1)
        (fun v => G.dist x v)
      have hA : ∑ v ∈ W.filter (fun v => G.dist x v = 1), G.dist x v =
          #(W.filter fun v => G.dist x v = 1) := by
        rw [card_eq_sum_ones]
        exact sum_congr rfl fun v hv => (mem_filter.mp hv).2
      have hB : ∑ v ∈ W.filter (fun v => ¬ G.dist x v = 1), G.dist x v =
          2 * #(W.filter fun v => ¬ G.dist x v = 1) := by
        rw [mul_comm, ← smul_eq_mul, ← sum_const]
        exact sum_congr rfl fun v hv => by
          have := hb v (mem_filter.mp hv).1; have := (mem_filter.mp hv).2; omega
      have := card_filter_add_card_filter_not (s := W) (fun v => G.dist x v = 1)
      omega
    intro S T hS hT
    rw [card_minTDS_two_regular hn hdeg hS, card_minTDS_two_regular hn hdeg hT]
  · -- diameter at least four is impossible
    exfalso
    have hE : 5 ≤ #G.edgeFinset := by
      have := hG.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, hn] at this
      omega
    have hsumdeg := G.sum_degrees_eq_twice_card_edges
    obtain ⟨x, hx⟩ : ∃ x, 2 ≤ G.degree x := by
      by_contra hcon
      push Not at hcon
      have : ∑ v, G.degree v ≤ ∑ _v : V, 1 := sum_le_sum fun v _ => by have := hcon v; omega
      simp only [sum_const, card_univ, hn, smul_eq_mul, mul_one] at this
      omega
    rw [← card_neighborFinset_eq_degree] at hx
    obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp hx
    rw [mem_neighborFinset] at hp hq
    obtain ⟨y, hxy, hT, hgeo⟩ := hstr x
    obtain ⟨hne, hc, hs, hb⟩ := hW x y hxy hT hgeo
    obtain ⟨r, -, hr⟩ := exists_pred hG (k := D - 1) (by omega : G.dist x y = D - 1 + 1)
    obtain ⟨s, -, hs'⟩ := exists_pred hG (k := D - 2) (by omega : G.dist x r = D - 2 + 1)
    have hp1 := dist_eq_one_iff_adj.mpr hp
    have hq1 := dist_eq_one_iff_adj.mpr hq
    set W := (univ.erase x).erase y
    have hmem : ∀ v, 1 ≤ G.dist x v → G.dist x v < D → v ∈ W := by
      intro v h1 h2
      simp only [W, mem_erase, mem_univ, and_true]
      refine ⟨?_, ?_⟩
      · rintro rfl; omega
      · rintro rfl; simp at h1
    have hsub : ({p, q, r, s} : Finset V) ⊆ W := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> exact hmem _ (by omega) (by omega)
    have hne' : ∀ a b : V, G.dist x a ≠ G.dist x b → a ≠ b := by rintro a b h rfl; exact h rfl
    have hpr := hne' p r (by omega)
    have hps := hne' p s (by omega)
    have hqr := hne' q r (by omega)
    have hqs := hne' q s (by omega)
    have hrs := hne' r s (by omega)
    have hcard : #({p, q, r, s} : Finset V) = 4 := by
      rw [card_insert_of_notMem (by simp [hpq, hpr, hps]),
        card_insert_of_notMem (by simp [hqr, hqs]), card_pair hrs]
    have heq := eq_of_subset_of_card_le hsub (by rw [hcard, hc])
    rw [← heq, sum_insert (by simp [hpq, hpr, hps]), sum_insert (by simp [hqr, hqs]),
      sum_pair hrs] at hs
    omega

/-! ### A checker for graphs on at most five vertices

A graph on the vertices `0, …, n - 1` is encoded by a number `c` whose bit `pidx i j` records
whether `i < j` are adjacent. Vertex sets are encoded as bit masks. The checker computes distances
by breadth-first search on masks and checks that all minimal total dominating sets have the same
size. The kernel runs it on every graph with two to five vertices. -/

/-- `f 0 ||| ⋯ ||| f (n - 1)`. -/
def orUpTo (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec 0 (fun k acc => acc ||| f k) n

/-- `f 0 + ⋯ + f (n - 1)`. -/
def sumUpTo (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec 0 (fun k acc => acc + f k) n

/-- Whether `p k` holds for every `k < n`. -/
def allUpTo (p : ℕ → Bool) (n : ℕ) : Bool := Nat.rec true (fun k acc => acc && p k) n

/-- Whether `p k` holds for some `k < n`. -/
def anyUpTo (p : ℕ → Bool) (n : ℕ) : Bool := Nat.rec false (fun k acc => acc || p k) n

/-- The bit recording the pair `i < j`. -/
def pidx (i j : ℕ) : ℕ := j * (j - 1) / 2 + i

/-- Adjacency in the graph encoded by `c`. -/
def adjB (c i j : ℕ) : Bool :=
  cond (Nat.blt i j) (c.testBit (pidx i j)) (cond (Nat.blt j i) (c.testBit (pidx j i)) false)

/-- The neighbourhood of `v`, as a mask. -/
def nbrMask (n c v : ℕ) : ℕ := orUpTo (fun k => cond (adjB c v k) (2 ^ k) 0) n

/-- One step of breadth-first search. -/
def expand (n c R : ℕ) : ℕ := R ||| orUpTo (fun v => cond (R.testBit v) (nbrMask n c v) 0) n

/-- The vertices at distance at most `k` from `i`. -/
def reach (n c i k : ℕ) : ℕ := Nat.rec (2 ^ i) (fun _ R => expand n c R) k

/-- The total distance of `i`: the number of pairs `(k, j)` with `d(i, j) > k`. -/
def tB (n c i : ℕ) : ℕ :=
  sumUpTo (fun k => sumUpTo (fun j => cond ((reach n c i k).testBit j) 0 1) n) n

/-- The eccentricity of `i`: the number of `k` such that some `j` has `d(i, j) > k`. -/
def eB (n c i : ℕ) : ℕ :=
  sumUpTo (fun k => cond (allUpTo (fun j => (reach n c i k).testBit j) n) 0 1) n

/-- Connectivity. -/
def connB (n c : ℕ) : Bool := allUpTo (fun j => (reach n c 0 n).testBit j) n

/-- The hypothesis of Conjecture 321. -/
def hypB (n c : ℕ) : Bool :=
  allUpTo (fun i => Nat.ble (n * tB n c i) (3 * sumUpTo (eB n c) n)) n

/-- The mask `m` is a total dominating set. -/
def tdsB (n c m : ℕ) : Bool :=
  allUpTo (fun v => anyUpTo (fun s => m.testBit s && adjB c v s) n) n

/-- The mask `m` is a minimal total dominating set. -/
def minB (n c m : ℕ) : Bool :=
  tdsB n c m && allUpTo (fun s => !m.testBit s || !tdsB n c (m ^^^ 2 ^ s)) n

/-- The number of vertices in the mask `m`. -/
def popB (n m : ℕ) : ℕ := sumUpTo (fun s => cond (m.testBit s) 1 0) n

/-- All minimal total dominating sets have the same size. -/
def wtdB (n c : ℕ) : Bool :=
  anyUpTo (fun k => allUpTo (fun m => !minB n c m || Nat.beq (popB n m) k) (2 ^ n)) (n + 1)

/-- Conjecture 321 for the graph encoded by `c`. -/
def check (n c : ℕ) : Bool := !(connB n c && hypB n c) || wtdB n c

set_option maxRecDepth 100000 in
theorem check_two : ∀ c < 2 ^ 1, check 2 c = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem check_three : ∀ c < 2 ^ 3, check 3 c = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem check_four : ∀ c < 2 ^ 6, check 4 c = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem check_five : ∀ c < 2 ^ 10, check 5 c = true := by decide +kernel


/-! ### Correctness of the checker -/

lemma testBit_orUpTo (f : ℕ → ℕ) (n m : ℕ) :
    (orUpTo f n).testBit m = true ↔ ∃ k < n, (f k).testBit m = true := by
  induction n with
  | zero => exact iff_of_false (by simp [orUpTo]) (by simp)
  | succ n ih =>
    show (orUpTo f n ||| f n).testBit m = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

lemma sumUpTo_eq (f : ℕ → ℕ) (n : ℕ) : sumUpTo f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

lemma allUpTo_eq_true (p : ℕ → Bool) (n : ℕ) : allUpTo p n = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => exact iff_of_true rfl fun k hk => absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    show (allUpTo p n && p n) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

lemma anyUpTo_eq_true (p : ℕ → Bool) (n : ℕ) : anyUpTo p n = true ↔ ∃ k < n, p k = true := by
  induction n with
  | zero => exact iff_of_false (by simp [anyUpTo]) (by simp)
  | succ n ih =>
    show (anyUpTo p n || p n) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

lemma pidx_inj_aux : allUpTo (fun j => allUpTo (fun i => allUpTo (fun j' => allUpTo (fun i' =>
    !Nat.beq (pidx i j) (pidx i' j') || (Nat.beq i i' && Nat.beq j j')) j') 5) j) 5 = true := by
  decide +kernel

lemma pidx_inj : ∀ j < 5, ∀ i < j, ∀ j' < 5, ∀ i' < j',
    pidx i j = pidx i' j' → i = i' ∧ j = j' := by
  intro j hj i hi j' hj' i' hi' h
  have := pidx_inj_aux
  simp only [allUpTo_eq_true] at this
  have := this j hj i hi j' hj' i' hi'
  simpa [Nat.beq_eq, h] using this

lemma pidx_lt_aux : allUpTo (fun n => allUpTo (fun j => allUpTo (fun i =>
    Nat.blt (pidx i j) (n * (n - 1) / 2)) j) n) 6 = true := by
  decide +kernel

lemma pidx_lt : ∀ n ≤ 5, ∀ j < n, ∀ i < j, pidx i j < n * (n - 1) / 2 := by
  intro n hn j hj i hi
  have := pidx_lt_aux
  simp only [allUpTo_eq_true] at this
  simpa [Nat.blt_eq] using this n (by omega) j hj i hi

lemma testBit_nbrMask (n c v j : ℕ) :
    (nbrMask n c v).testBit j = true ↔ j < n ∧ adjB c v j = true := by
  simp only [nbrMask, testBit_orUpTo]
  constructor
  · rintro ⟨k, hk, h⟩
    cases hb : adjB c v k
    · simp [hb] at h
    · rw [hb, Bool.cond_true, Nat.testBit_two_pow, decide_eq_true_iff] at h
      subst h
      exact ⟨hk, hb⟩
  · rintro ⟨hj, hb⟩
    exact ⟨j, hj, by rw [hb, Bool.cond_true, Nat.testBit_two_pow_self]⟩

lemma sum_range_ite_le (d n : ℕ) (h : d ≤ n) :
    ∑ k ∈ range n, (if d ≤ k then 0 else 1) = d := by
  rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one]
  rw [show (range n).filter (fun k => ¬ d ≤ k) = range d by ext k; simp; omega, card_range]

omit [Fintype V] in
lemma exists_walk_le_succ (G : SimpleGraph V) {a b : V} {k : ℕ} :
    (∃ p : G.Walk a b, p.length ≤ k + 1) ↔
      (∃ p : G.Walk a b, p.length ≤ k) ∨ ∃ w, (∃ p : G.Walk a w, p.length ≤ k) ∧ G.Adj w b := by
  constructor
  · rintro ⟨p, hp⟩
    by_cases hk : p.length ≤ k
    · exact Or.inl ⟨p, hk⟩
    · have hnil : ¬ p.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
      refine Or.inr ⟨p.penultimate, ⟨p.dropLast, ?_⟩, p.adj_penultimate hnil⟩
      rw [Walk.length_dropLast]
      omega
  · rintro (⟨p, hp⟩ | ⟨w, ⟨p, hp⟩, h⟩)
    · exact ⟨p, by omega⟩
    · exact ⟨p.concat h, by rw [Walk.length_concat]; omega⟩

omit [Fintype V] in
lemma exists_walk_le_iff {G : SimpleGraph V} (hG : G.Connected) (a b : V) (k : ℕ) :
    (∃ p : G.Walk a b, p.length ≤ k) ↔ G.dist a b ≤ k := by
  constructor
  · rintro ⟨p, hp⟩
    exact (dist_le p).trans hp
  · intro h
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a b
    exact ⟨p, hp ▸ h⟩

lemma dist_lt_card {G : SimpleGraph V} (hG : G.Connected) (a b : V) :
    G.dist a b < Fintype.card V := by
  obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist a b
  rw [← hl]
  exact hp.length_lt

lemma ecc_lt_card {G : SimpleGraph V} (hG : G.Connected) [Nonempty V] (v : V) :
    ecc G v < Fintype.card V := by
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  rw [← hw]
  exact dist_lt_card hG v w

section Encoding

variable (x₀ : V)

/-- The vertex numbered `i` (or `x₀` if `i ≥ |V|`). -/
def vtx (i : ℕ) : V := if h : i < Fintype.card V then (Fintype.equivFin V).symm ⟨i, h⟩ else x₀

/-- The number of the vertex `u`. -/
def idx (u : V) : ℕ := Fintype.equivFin V u

omit [Fintype V] in
lemma idx_lt [Fintype V] (u : V) : idx u < Fintype.card V := (Fintype.equivFin V u).2

lemma vtx_idx (u : V) : vtx x₀ (idx u) = u := by
  simp [vtx, idx]

lemma idx_vtx {i : ℕ} (hi : i < Fintype.card V) : idx (vtx x₀ i) = i := by
  simp [vtx, idx, hi]

lemma vtx_inj {i j : ℕ} (hi : i < Fintype.card V) (hj : j < Fintype.card V)
    (h : vtx x₀ i = vtx x₀ j) : i = j := by
  rw [← idx_vtx x₀ hi, ← idx_vtx x₀ hj, h]

lemma sum_range_vtx {M : Type*} [AddCommMonoid M] (f : V → M) :
    ∑ i ∈ range (Fintype.card V), f (vtx x₀ i) = ∑ u, f u := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (vtx x₀ i)),
    ← (Fintype.equivFin V).symm.sum_comp f]
  refine sum_congr rfl fun i _ => ?_
  simp [vtx, i.2]

variable (G : SimpleGraph V)

/-- The code of `G`, with vertices numbered by `idx`. -/
def code : ℕ :=
  orUpTo (fun j => orUpTo (fun i => if G.Adj (vtx x₀ i) (vtx x₀ j) then 2 ^ pidx i j else 0) j)
    (Fintype.card V)

lemma testBit_code (m : ℕ) : (code x₀ G).testBit m = true ↔
    ∃ j < Fintype.card V, ∃ i < j, G.Adj (vtx x₀ i) (vtx x₀ j) ∧ pidx i j = m := by
  simp only [code, testBit_orUpTo]
  refine exists_congr fun j => and_congr_right fun _ => exists_congr fun i =>
    and_congr_right fun _ => ?_
  split_ifs with h
  · simp [Nat.testBit_two_pow, h]
  · simp [h]

lemma adjB_code (hn : Fintype.card V ≤ 5) {i j : ℕ} (hi : i < Fintype.card V)
    (hj : j < Fintype.card V) : adjB (code x₀ G) i j = true ↔ G.Adj (vtx x₀ i) (vtx x₀ j) := by
  unfold adjB
  rcases lt_trichotomy i j with h | rfl | h
  · rw [show Nat.blt i j = true by simpa [Nat.blt_eq] using h, Bool.cond_true, testBit_code]
    constructor
    · rintro ⟨j', hj', i', hi', hadj, heq⟩
      obtain ⟨rfl, rfl⟩ := pidx_inj j' (by omega) i' hi' j (by omega) i h heq
      exact hadj
    · intro hadj
      exact ⟨j, hj, i, h, hadj, rfl⟩
  · simp
  · rw [show Nat.blt i j = false by
        rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; omega, Bool.cond_false,
      show Nat.blt j i = true by simpa [Nat.blt_eq] using h, Bool.cond_true, testBit_code, G.adj_comm]
    constructor
    · rintro ⟨i', hi', j', hj', hadj, heq⟩
      obtain ⟨rfl, rfl⟩ := pidx_inj i' (by omega) j' hj' i (by omega) j h heq
      exact hadj
    · intro hadj
      exact ⟨i, hi, j, h, hadj, rfl⟩

lemma code_lt (hn : Fintype.card V ≤ 5) :
    code x₀ G < 2 ^ (Fintype.card V * (Fintype.card V - 1) / 2) := by
  apply Nat.lt_pow_two_of_testBit
  intro m hm
  by_contra h
  rw [Bool.not_eq_false, testBit_code] at h
  obtain ⟨j, hj, i, hi, -, rfl⟩ := h
  have := pidx_lt _ hn j hj i hi
  omega

lemma testBit_reach (hn : Fintype.card V ≤ 5) {i : ℕ} (hi : i < Fintype.card V) (k j : ℕ) :
    (reach (Fintype.card V) (code x₀ G) i k).testBit j = true ↔
      j < Fintype.card V ∧ ∃ p : G.Walk (vtx x₀ i) (vtx x₀ j), p.length ≤ k := by
  induction k generalizing j with
  | zero =>
    show (2 ^ i).testBit j = true ↔ _
    rw [Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro rfl
      exact ⟨hi, Walk.nil, le_refl _⟩
    · rintro ⟨hj, p, hp⟩
      exact vtx_inj x₀ hi hj (Walk.eq_of_length_eq_zero (by omega : p.length = 0))
  | succ k ih =>
    show (expand (Fintype.card V) (code x₀ G)
      (reach (Fintype.card V) (code x₀ G) i k)).testBit j = true ↔ _
    rw [expand, Nat.testBit_or, Bool.or_eq_true, testBit_orUpTo, ih, exists_walk_le_succ]
    constructor
    · rintro (h | ⟨v, hv, h⟩)
      · exact ⟨h.1, Or.inl h.2⟩
      · cases hR : (reach (Fintype.card V) (code x₀ G) i k).testBit v
        · simp [hR] at h
        · rw [hR, Bool.cond_true, testBit_nbrMask] at h
          obtain ⟨hj, hadj⟩ := h
          obtain ⟨-, p, hp⟩ := (ih v).mp hR
          exact ⟨hj, Or.inr ⟨vtx x₀ v, ⟨p, hp⟩, (adjB_code x₀ G hn hv hj).mp hadj⟩⟩
    · rintro ⟨hj, h | ⟨w, ⟨p, hp⟩, hadj⟩⟩
      · exact Or.inl ⟨hj, h⟩
      · refine Or.inr ⟨idx w, idx_lt w, ?_⟩
        have hR : (reach (Fintype.card V) (code x₀ G) i k).testBit (idx w) = true :=
          (ih (idx w)).mpr ⟨idx_lt w, by rw [vtx_idx]; exact ⟨p, hp⟩⟩
        rw [hR, Bool.cond_true, testBit_nbrMask]
        exact ⟨hj, (adjB_code x₀ G hn (idx_lt w) hj).mpr (by rw [vtx_idx]; exact hadj)⟩

variable {G}

lemma testBit_reach_dist (hG : G.Connected) (hn : Fintype.card V ≤ 5) {i : ℕ}
    (hi : i < Fintype.card V) (k j : ℕ) :
    (reach (Fintype.card V) (code x₀ G) i k).testBit j = true ↔
      j < Fintype.card V ∧ G.dist (vtx x₀ i) (vtx x₀ j) ≤ k := by
  rw [testBit_reach x₀ G hn hi, exists_walk_le_iff hG]

lemma tB_eq (hG : G.Connected) (hn : Fintype.card V ≤ 5) {i : ℕ} (hi : i < Fintype.card V) :
    tB (Fintype.card V) (code x₀ G) i = Tdist G (vtx x₀ i) := by
  have key : ∀ k j, j < Fintype.card V →
      cond ((reach (Fintype.card V) (code x₀ G) i k).testBit j) 0 1 =
        if G.dist (vtx x₀ i) (vtx x₀ j) ≤ k then 0 else 1 := by
    intro k j hj
    have h := testBit_reach_dist x₀ hG hn hi k j
    by_cases hd : G.dist (vtx x₀ i) (vtx x₀ j) ≤ k
    · rw [ite_eq_left hd, h.mpr ⟨hj, hd⟩, Bool.cond_true]
    · rw [ite_eq_right hd]
      have : (reach (Fintype.card V) (code x₀ G) i k).testBit j = false := by
        by_contra h'
        rw [Bool.not_eq_false] at h'
        exact hd (h.mp h').2
      rw [this, Bool.cond_false]
  simp only [tB, sumUpTo_eq]
  rw [sum_congr rfl fun k _ => sum_congr rfl fun j hj => key k j (mem_range.mp hj), sum_comm,
    sum_congr rfl fun j _ => sum_range_ite_le _ _ (dist_lt_card hG _ _).le]
  exact sum_range_vtx x₀ (fun u => G.dist (vtx x₀ i) u)

lemma eB_eq (hG : G.Connected) (hn : Fintype.card V ≤ 5) {i : ℕ} (hi : i < Fintype.card V) :
    eB (Fintype.card V) (code x₀ G) i = ecc G (vtx x₀ i) := by
  have key : ∀ k, cond (allUpTo (fun j => (reach (Fintype.card V) (code x₀ G) i k).testBit j)
      (Fintype.card V)) 0 1 = if ecc G (vtx x₀ i) ≤ k then 0 else 1 := by
    intro k
    have hiff : allUpTo (fun j => (reach (Fintype.card V) (code x₀ G) i k).testBit j)
        (Fintype.card V) = true ↔ ecc G (vtx x₀ i) ≤ k := by
      rw [allUpTo_eq_true, ecc, Finset.sup_le_iff]
      constructor
      · intro h u _
        have := (testBit_reach_dist x₀ hG hn hi k (idx u)).mp (h _ (idx_lt u))
        rw [vtx_idx] at this
        exact this.2
      · intro h j hj
        exact (testBit_reach_dist x₀ hG hn hi k j).mpr ⟨hj, h _ (mem_univ _)⟩
    by_cases hd : ecc G (vtx x₀ i) ≤ k
    · rw [ite_eq_left hd, hiff.mpr hd, Bool.cond_true]
    · rw [ite_eq_right hd]
      have : allUpTo (fun j => (reach (Fintype.card V) (code x₀ G) i k).testBit j)
          (Fintype.card V) = false := by
        by_contra h'
        rw [Bool.not_eq_false] at h'
        exact hd (hiff.mp h')
      rw [this, Bool.cond_false]
  have : Nonempty V := ⟨x₀⟩
  simp only [eB, sumUpTo_eq]
  rw [sum_congr rfl fun k _ => key k]
  exact sum_range_ite_le _ _ (ecc_lt_card hG _).le

lemma hypB_true (hG : G.Connected) (hn : Fintype.card V ≤ 5)
    (hyp : ∀ w, Fintype.card V * Tdist G w ≤ 3 * ∑ v, ecc G v) :
    hypB (Fintype.card V) (code x₀ G) = true := by
  have hsum : sumUpTo (eB (Fintype.card V) (code x₀ G)) (Fintype.card V) = ∑ v, ecc G v := by
    rw [sumUpTo_eq, ← sum_range_vtx x₀ (ecc G)]
    exact sum_congr rfl fun i hi => eB_eq x₀ hG hn (mem_range.mp hi)
  rw [hypB, allUpTo_eq_true]
  intro i hi
  rw [Nat.ble_eq, tB_eq x₀ hG hn hi, hsum]
  exact hyp _

lemma connB_true (hG : G.Connected) (hn : Fintype.card V ≤ 5) :
    connB (Fintype.card V) (code x₀ G) = true := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x₀⟩
  rw [connB, allUpTo_eq_true]
  intro j hj
  exact (testBit_reach_dist x₀ hG hn hpos _ j).mpr ⟨hj, (dist_lt_card hG _ _).le⟩

/-- The mask of a vertex set. -/
def maskOf (S : Finset V) : ℕ :=
  orUpTo (fun i => if vtx x₀ i ∈ S then 2 ^ i else 0) (Fintype.card V)

lemma testBit_maskOf (S : Finset V) (j : ℕ) :
    (maskOf x₀ S).testBit j = true ↔ j < Fintype.card V ∧ vtx x₀ j ∈ S := by
  simp only [maskOf, testBit_orUpTo]
  constructor
  · rintro ⟨k, hk, h⟩
    split_ifs at h with hS
    · rw [Nat.testBit_two_pow, decide_eq_true_iff] at h
      subst h
      exact ⟨hk, hS⟩
    · simp at h
  · rintro ⟨hj, hS⟩
    exact ⟨j, hj, by rw [ite_eq_left hS, Nat.testBit_two_pow_self]⟩

lemma maskOf_lt (S : Finset V) : maskOf x₀ S < 2 ^ Fintype.card V := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  by_contra h
  rw [Bool.not_eq_false, testBit_maskOf] at h
  omega

lemma tdsB_maskOf (hn : Fintype.card V ≤ 5) (S : Finset V) :
    tdsB (Fintype.card V) (code x₀ G) (maskOf x₀ S) = true ↔ IsTDS G S := by
  rw [tdsB, allUpTo_eq_true]
  simp only [anyUpTo_eq_true, Bool.and_eq_true, testBit_maskOf]
  constructor
  · intro h u
    obtain ⟨s, hs, ⟨-, hsS⟩, hadj⟩ := h (idx u) (idx_lt u)
    rw [adjB_code x₀ G hn (idx_lt u) hs, vtx_idx] at hadj
    exact ⟨_, hsS, hadj⟩
  · intro h v hv
    obtain ⟨w, hw, hadj⟩ := h (vtx x₀ v)
    refine ⟨idx w, idx_lt w, ⟨idx_lt w, by rwa [vtx_idx]⟩, ?_⟩
    rw [adjB_code x₀ G hn hv (idx_lt w), vtx_idx]
    exact hadj

lemma maskOf_erase {S : Finset V} {a : V} (ha : a ∈ S) :
    maskOf x₀ S ^^^ 2 ^ idx a = maskOf x₀ (S.erase a) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : idx a = j
  · subst hj
    have h1 : (maskOf x₀ S).testBit (idx a) = true :=
      (testBit_maskOf x₀ S _).mpr ⟨idx_lt a, by rwa [vtx_idx]⟩
    have h2 : (maskOf x₀ (S.erase a)).testBit (idx a) = false := by
      by_contra h
      rw [Bool.not_eq_false, testBit_maskOf, vtx_idx] at h
      simp at h
    rw [h1, h2]
    simp
  · rw [decide_eq_false hj, Bool.xor_false, Bool.eq_iff_iff, testBit_maskOf, testBit_maskOf,
      mem_erase]
    constructor
    · rintro ⟨hjn, hS⟩
      refine ⟨hjn, fun h => hj ?_, hS⟩
      rw [← h, idx_vtx x₀ hjn]
    · rintro ⟨hjn, -, hS⟩
      exact ⟨hjn, hS⟩

lemma minB_maskOf (hn : Fintype.card V ≤ 5) {S : Finset V} (hS : IsMinTDS G S) :
    minB (Fintype.card V) (code x₀ G) (maskOf x₀ S) = true := by
  rw [minB, Bool.and_eq_true, tdsB_maskOf x₀ hn, allUpTo_eq_true]
  refine ⟨hS.1, fun s hs => ?_⟩
  cases hb : (maskOf x₀ S).testBit s
  · simp
  · have hmem := ((testBit_maskOf x₀ S s).mp hb).2
    have hm := maskOf_erase x₀ hmem
    rw [idx_vtx x₀ hs] at hm
    have hnot : tdsB (Fintype.card V) (code x₀ G) (maskOf x₀ (S.erase (vtx x₀ s))) = false := by
      by_contra h
      rw [Bool.not_eq_false, tdsB_maskOf x₀ hn] at h
      exact hS.2 _ (erase_ssubset hmem) h
    rw [hm, hnot]
    rfl

lemma popB_maskOf (S : Finset V) : popB (Fintype.card V) (maskOf x₀ S) = #S := by
  rw [popB, sumUpTo_eq]
  have : ∀ s ∈ range (Fintype.card V),
      cond ((maskOf x₀ S).testBit s) 1 0 = if vtx x₀ s ∈ S then 1 else 0 := by
    intro s hs
    by_cases h : vtx x₀ s ∈ S
    · rw [ite_eq_left h, (testBit_maskOf x₀ S s).mpr ⟨mem_range.mp hs, h⟩, Bool.cond_true]
    · rw [ite_eq_right h]
      have : (maskOf x₀ S).testBit s = false := by
        by_contra h'
        rw [Bool.not_eq_false, testBit_maskOf] at h'
        exact h h'.2
      rw [this, Bool.cond_false]
  rw [sum_congr rfl this, sum_range_vtx x₀ (fun u => if u ∈ S then 1 else 0)]
  simp

lemma wtd_of_wtdB (hn : Fintype.card V ≤ 5) (h : wtdB (Fintype.card V) (code x₀ G) = true) :
    WellTotallyDominated G := by
  rw [wtdB, anyUpTo_eq_true] at h
  obtain ⟨k, -, hk⟩ := h
  rw [allUpTo_eq_true] at hk
  have hS : ∀ S, IsMinTDS G S → #S = k := by
    intro S hS
    have := hk _ (maskOf_lt x₀ S)
    rw [minB_maskOf x₀ hn hS, Bool.not_true, Bool.false_or, Nat.beq_eq, popB_maskOf] at this
    exact this
  intro S T h1 h2
  rw [hS S h1, hS T h2]

end Encoding

/-- Conjecture 321 for graphs with two to five vertices. -/
theorem wtd_small {G : SimpleGraph V} (hG : G.Connected) (h1 : 1 < Fintype.card V)
    (h5 : Fintype.card V ≤ 5) (hyp : ∀ w, Fintype.card V * Tdist G w ≤ 3 * ∑ v, ecc G v) :
    WellTotallyDominated G := by
  obtain ⟨x₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hc := code_lt x₀ G h5
  have hconn := connB_true x₀ hG h5
  have hhyp := hypB_true x₀ hG h5 hyp
  have hchk : check (Fintype.card V) (code x₀ G) = true := by
    obtain ⟨c, hcdef⟩ : ∃ c, code x₀ G = c := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n := ⟨_, rfl⟩
    rw [hcdef, hn] at hc ⊢
    rw [hn] at h1 h5
    interval_cases n
    · exact check_two c (by simpa using hc)
    · exact check_three c (by simpa using hc)
    · exact check_four c (by simpa using hc)
    · exact check_five c (by simpa using hc)
  rw [check, hconn, hhyp] at hchk
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hchk
  exact wtd_of_wtdB x₀ h5 hchk

/-- **WOWII Conjecture 321.** -/
theorem conjecture321 : Conjecture321 := by
  intro V _ G hG h1 h
  have hyp := hyp_nat (by omega) h
  have h6 := card_le_six hG h1 hyp
  rcases (by omega : Fintype.card V = 6 ∨ Fintype.card V ≤ 5) with h6' | h5
  · exact wtd_six hG h6' hyp
  · exact wtd_small hG h1 h5 hyp

end WOWII321
