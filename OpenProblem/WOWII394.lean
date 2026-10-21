import OpenProblem.WOWII281
import OpenProblem.WOWII382b
import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 394 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 394.** If `G` is a connected graph on `n > 2` vertices, then
> `γ_2 ≤ μ(G) + |E(G[A_2])| + |M|`, where `M` is the set of vertices of minimum local
> independence and `A_2` is the set of vertices of degree two.

Here `γ_2` is the 2-domination number, `μ` the matching number and `λ(v) = α(G[N(v)])` the local
independence.

The counterexample `G12'` has 12 vertices and 15 edges and was found by simulated annealing:

* a 4-cycle `3 - 1 - 5 - 2 - 3` with a leaf `4` at `5`;
* the edge `3 - 6`, joining it to the part `R = {0, 6, 7, 8, 9, 10, 11}` with edges
  `0-6, 0-7, 0-10, 6-9, 6-11, 7-8, 7-9, 8-11, 10-11`.

We verify the four quantities.

* `λ = 1` only at the leaf `4`, so `|M| = 1`.
* The degree-two vertices `1, 2, 8, 9, 10` are pairwise non-adjacent, so `E(G[A_2]) = ∅`.
* `μ ≤ 5`. A perfect matching would match `4` to `5`, and then both `1` and `2` to `3`.
* `γ_2 ≥ 7`. A 2-dominating set has at least three vertices among `1, …, 5` and at least four in
  `R`, because the vertices of `R` other than `6` have all their neighbours in `R`.

So the bound is at most `6 < 7`. The conjecture holds for all connected graphs up to 9 vertices,
and annealing finds counterexamples at 12 vertices but none at 11.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII394

open WOWII178 WOWII326 WOWII382b

variable {V : Type*} [Fintype V]

/-- The vertices of minimum local independence. -/
def minLamSet (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => localIndep G v = WOWII162.minLocalIndep G

/-- The vertices of degree two. -/
def A2 (G : SimpleGraph V) : Finset V := univ.filter fun v => G.degree v = 2

/-- The statement of Conjecture 394. -/
def Conjecture394 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ matchingNumber G + WOWII449.edgesIn G (A2 G) + #(minLamSet G)

/-- A matching with `card V / 2` edges covers every vertex. -/
lemma covers {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    (hcard : 2 * #M = Fintype.card V) (v : V) : ∃ e ∈ M, v ∈ e := by
  by_contra hno
  push Not at hno
  have h1 : ∀ e ∈ M, #(univ.filter fun w => w ∈ e) = 2 := by
    intro e he
    have heG := hM.1 he
    rw [mem_edgeFinset] at heG
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := G.ne_of_adj heG
      rw [show (univ.filter fun w => w ∈ s(a, b)) = {a, b} by ext; simp [Sym2.mem_iff]]
      exact card_pair hab
  have h2 : ∀ w, #(M.filter fun e => w ∈ e) ≤ 1 := by
    intro w
    rw [card_le_one]
    intro e he f hf
    by_contra hef
    exact hM.2 e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hef w (mem_filter.mp he).2
      (mem_filter.mp hf).2
  have hv : #(M.filter fun e => v ∈ e) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun e he => hno e he
  have hsum : ∑ e ∈ M, #(univ.filter fun w => w ∈ e) = ∑ w, #(M.filter fun e => w ∈ e) := by
    simp_rw [card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [sum_congr rfl h1, sum_const, smul_eq_mul, ← add_sum_erase _ _ (mem_univ v), hv,
    zero_add] at hsum
  have h3 : ∑ w ∈ univ.erase v, #(M.filter fun e => w ∈ e) ≤ ∑ _w ∈ univ.erase v, 1 :=
    sum_le_sum fun w _ => h2 w
  rw [sum_const, card_erase_of_mem (mem_univ v), card_univ, smul_eq_mul, mul_one] at h3
  have := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-! ### The counterexample -/

def E12 : List (Fin 12 × Fin 12) :=
  [(0, 6), (0, 7), (0, 10), (1, 3), (1, 5), (2, 3), (2, 5), (3, 6), (4, 5), (6, 9), (6, 11),
    (7, 8), (7, 9), (8, 11), (10, 11)]

def adjB (a b : Fin 12) : Bool := E12.contains (a, b) || E12.contains (b, a)

def G : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 12} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 12, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_degree (v : Fin 12) : G.degree v = #(univ.filter fun w => adjB v w = true) := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G_adj]

/-- A neighbour closer to `6`, and the distance from `6`. -/
def par : Fin 12 → Fin 12 := ![6, 3, 3, 6, 5, 1, 6, 0, 7, 6, 0, 6]
def dist6 : Fin 12 → ℕ := ![1, 2, 2, 1, 4, 3, 0, 2, 3, 1, 2, 1]

lemma G_connected : G.Connected := by
  refine WOWII267.connected_of_parent 6 dist6 par fun v hv => ?_
  rw [G_adj]
  revert v
  decide

lemma G_A2 : WOWII449.edgesIn G (A2 G) = 0 := by
  have hA : A2 G = {1, 2, 8, 9, 10} := by
    ext v
    simp only [A2, mem_filter, mem_univ, true_and, G_degree]
    revert v
    decide
  rw [WOWII449.edgesIn, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he'
  simp only [mem_filter] at he'
  obtain ⟨he, hall⟩ := he'
  rw [mem_edgeFinset] at he
  induction e using Sym2.ind with
  | h a b =>
    have ha := hall a (Sym2.mem_mk_left a b)
    have hb := hall b (Sym2.mem_mk_right a b)
    rw [hA] at ha hb
    have := G_adj.mp he
    revert this
    have key : ∀ a ∈ ({1, 2, 8, 9, 10} : Finset (Fin 12)), ∀ b ∈ ({1, 2, 8, 9, 10} : Finset (Fin 12)),
        adjB a b = false := by decide
    rw [key a ha b hb]
    exact Bool.false_ne_true

lemma localIndep_four : localIndep G 4 ≤ 1 := by
  have := WOWII162.localIndep_le_degree G 4
  rw [G_degree] at this
  exact this.trans (by decide)

lemma two_le_localIndep (v : Fin 12) (hv : v ≠ 4) : 2 ≤ localIndep G v := by
  have h : ∀ v : Fin 12, v ≠ 4 → ∃ a b : Fin 12, a ≠ b ∧ adjB v a = true ∧ adjB v b = true ∧
      adjB a b = false := by decide
  obtain ⟨a, b, hab, ha, hb, hnab⟩ := h v hv
  have := WOWII96.card_le_localIndep G v (A := {a, b})
    (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact G_adj.mpr ha
      · rw [mem_singleton.mp hx]; exact G_adj.mpr hb)
    (by
      intro x hx y hy hxy
      rw [G_adj] at hxy
      have hirr : ∀ z : Fin 12, adjB z z = false := by decide
      have hsymm : ∀ z z' : Fin 12, adjB z z' = adjB z' z := by decide
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hxy
      · rw [hirr] at hxy; exact Bool.false_ne_true hxy
      · rw [hnab] at hxy; exact Bool.false_ne_true hxy
      · rw [hsymm, hnab] at hxy; exact Bool.false_ne_true hxy
      · rw [hirr] at hxy; exact Bool.false_ne_true hxy)
  rwa [card_pair hab] at this

lemma G_minLamSet : #(minLamSet G) = 1 := by
  have hmin : WOWII162.minLocalIndep G = localIndep G 4 := by
    apply le_antisymm (Nat.sInf_le (Set.mem_range_self 4))
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨v, rfl⟩
    by_cases hv : v = 4
    · rw [hv]
    · have := two_le_localIndep v hv
      have := localIndep_four
      omega
  rw [minLamSet, hmin, card_eq_one]
  refine ⟨4, ?_⟩
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    by_contra hv
    have := two_le_localIndep v hv
    have := localIndep_four
    omega
  · rintro rfl
    rfl

/-- A neighbour of a vertex with a given neighbourhood. -/
lemma partner {e : Sym2 (Fin 12)} {v : Fin 12} (he : e ∈ G.edgeFinset) (hv : v ∈ e) :
    ∃ w, adjB v w = true ∧ e = s(v, w) := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
  exact ⟨w, G_adj.mp (mem_edgeFinset.mp he), rfl⟩

lemma G_matchingNumber : matchingNumber G ≤ 5 := by
  obtain ⟨M, hM, hcard⟩ := exists_max_matching G
  have h2 := WOWII281.two_mul_card_le hM
  rw [Fintype.card_fin] at h2
  rw [← hcard]
  by_contra hlt
  have h6 : 2 * #M = Fintype.card (Fin 12) := by rw [Fintype.card_fin]; omega
  obtain ⟨e4, he4, h4⟩ := covers hM h6 4
  obtain ⟨e1, he1, h1⟩ := covers hM h6 1
  obtain ⟨e2, he2, h2'⟩ := covers hM h6 2
  obtain ⟨w4, hw4, rfl⟩ := partner (hM.1 he4) h4
  obtain ⟨w1, hw1, rfl⟩ := partner (hM.1 he1) h1
  obtain ⟨w2, hw2, rfl⟩ := partner (hM.1 he2) h2'
  have hw4' : w4 = 5 := (by decide : ∀ w : Fin 12, adjB 4 w = true → w = 5) w4 hw4
  have hw1' : w1 = 3 ∨ w1 = 5 :=
    (by decide : ∀ w : Fin 12, adjB 1 w = true → w = 3 ∨ w = 5) w1 hw1
  have hw2' : w2 = 3 ∨ w2 = 5 :=
    (by decide : ∀ w : Fin 12, adjB 2 w = true → w = 3 ∨ w = 5) w2 hw2
  subst hw4'
  -- `1` and `2` cannot use `5`
  have hne : ∀ x : Fin 12, x ≠ 4 → s(x, 5) ∈ M → False := by
    intro x hx hxM
    have hdiff : s(x, 5) ≠ s((4 : Fin 12), 5) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hx h1
      · exact absurd h2 (by decide)
    exact hM.2 _ hxM _ he4 hdiff 5 (Sym2.mem_mk_right _ _) (Sym2.mem_mk_right _ _)
  have h1' : w1 = 3 := hw1'.resolve_right fun h => hne 1 (by decide) (h ▸ he1)
  have h2'' : w2 = 3 := hw2'.resolve_right fun h => hne 2 (by decide) (h ▸ he2)
  subst h1'
  subst h2''
  have hdiff : s((1 : Fin 12), 3) ≠ s((2 : Fin 12), 3) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by decide)
  exact hM.2 _ he1 _ he2 hdiff 3 (Sym2.mem_mk_right _ _) (Sym2.mem_mk_right _ _)

lemma filt_le {S : Finset (Fin 12)} {v : Fin 12} (T : Finset (Fin 12))
    (hN : ∀ w, adjB v w = true → w ∈ S → w ∈ T) : #(S.filter (G.Adj v)) ≤ #T :=
  card_le_card fun w hw => hN w (G_adj.mp (mem_filter.mp hw).2) (mem_filter.mp hw).1

/-- A vertex outside a 2-dominating set has two neighbours in it. -/
lemma lt_two {S : Finset (Fin 12)} (hS : IsTwoDom G S) {v a : Fin 12} (hv : v ∉ S)
    (hN : ∀ w, adjB v w = true → w ∈ S → w = a) : False := by
  have h1 := hS v hv
  have h2 := filt_le (S := S) (v := v) {a} fun w hw hwS => mem_singleton.mpr (hN w hw hwS)
  rw [card_singleton] at h2
  omega

/-- Every 2-dominating set of `G` has at least seven vertices. -/
lemma G_twoDomNum : 7 ≤ twoDomNum G := by
  have hne : {k | ∃ S, IsTwoDom G S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  rw [twoDomNum, ← hcard]
  -- local constraints
  have nb : ∀ v : Fin 12, ∀ L : List (Fin 12), (∀ w, adjB v w = true → w ∈ L) → v ∉ S →
      ∀ a ∈ L, (∀ b ∈ L, b ≠ a → b ∉ S) → False := by
    intro v L hL hv a _ hothers
    refine lt_two hS hv (a := a) fun w hw hwS => ?_
    by_contra hwa
    exact hothers w (hL w hw) hwa hwS
  have h4 : (4 : Fin 12) ∈ S := by
    by_contra h
    exact nb 4 [5] (by decide) h 5 (by simp) (by simp)
  have two : ∀ v a b : Fin 12, (∀ w, adjB v w = true → w ∈ [a, b]) → a ≠ b → v ∉ S →
      a ∈ S ∧ b ∈ S := by
    intro v a b hL hab hv
    constructor
    · by_contra ha
      exact nb v [a, b] hL hv b (by simp) fun c hc hcb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ha
        · exact absurd rfl hcb
    · by_contra hb
      exact nb v [a, b] hL hv a (by simp) fun c hc hca => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact absurd rfl hca
        · exact hb
  let Q : Finset (Fin 12) := {1, 2, 3, 4, 5}
  let R : Finset (Fin 12) := {0, 6, 7, 8, 9, 10, 11}
  have sub : ∀ (P T : Finset (Fin 12)), T ⊆ S → T ⊆ P → #T ≤ #(S ∩ P) := fun P T h1 h2 =>
    card_le_card (subset_inter h1 h2)
  -- three vertices among `1, …, 5`
  have hQ : 3 ≤ #(S ∩ Q) := by
    by_cases h12 : (1 : Fin 12) ∈ S ∧ (2 : Fin 12) ∈ S
    · have := sub Q {1, 2, 4} (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h12.1
        · exact h12.2
        · exact h4) (by decide)
      exact this.trans' (by decide)
    · have h35 : (3 : Fin 12) ∈ S ∧ (5 : Fin 12) ∈ S := by
        by_cases h1 : (1 : Fin 12) ∈ S
        · have h2 : (2 : Fin 12) ∉ S := fun h2 => h12 ⟨h1, h2⟩
          exact two 2 3 5 (by decide) (by decide) h2
        · exact two 1 3 5 (by decide) (by decide) h1
      have := sub Q {3, 4, 5} (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h35.1
        · exact h4
        · exact h35.2) (by decide)
      exact this.trans' (by decide)
  -- four vertices in `R`
  have four : ∀ a b c d : Fin 12, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      ({a, b, c, d} : Finset (Fin 12)) ⊆ R → #({a, b, c, d} : Finset (Fin 12)) = 4 →
      4 ≤ #(S ∩ R) := by
    intro a b c d ha hb hc hd hR h4'
    rw [← h4']
    apply sub R _ _ hR
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hR : 4 ≤ #(S ∩ R) := by
    by_cases h8 : (8 : Fin 12) ∈ S
    · by_cases h9 : (9 : Fin 12) ∈ S
      · by_cases h10 : (10 : Fin 12) ∈ S
        · by_cases h0 : (0 : Fin 12) ∈ S
          · exact four 0 8 9 10 h0 h8 h9 h10 (by decide) (by decide)
          · by_cases h6 : (6 : Fin 12) ∈ S
            · exact four 6 8 9 10 h6 h8 h9 h10 (by decide) (by decide)
            · by_cases h7 : (7 : Fin 12) ∈ S
              · exact four 7 8 9 10 h7 h8 h9 h10 (by decide) (by decide)
              · exact (nb 0 [6, 7, 10] (by decide) h0 10 (by simp) (by
                  intro b hb hb10
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
                  rcases hb with rfl | rfl | rfl
                  · exact h6
                  · exact h7
                  · exact absurd rfl hb10)).elim
        · obtain ⟨h0, h11⟩ := two 10 0 11 (by decide) (by decide) h10
          exact four 0 8 9 11 h0 h8 h9 h11 (by decide) (by decide)
      · obtain ⟨h6, h7⟩ := two 9 6 7 (by decide) (by decide) h9
        by_cases h10 : (10 : Fin 12) ∈ S
        · exact four 6 7 8 10 h6 h7 h8 h10 (by decide) (by decide)
        · obtain ⟨h0, -⟩ := two 10 0 11 (by decide) (by decide) h10
          exact four 0 6 7 8 h0 h6 h7 h8 (by decide) (by decide)
    · obtain ⟨h7, h11⟩ := two 8 7 11 (by decide) (by decide) h8
      by_cases h9 : (9 : Fin 12) ∈ S
      · by_cases h10 : (10 : Fin 12) ∈ S
        · exact four 7 9 10 11 h7 h9 h10 h11 (by decide) (by decide)
        · obtain ⟨h0, -⟩ := two 10 0 11 (by decide) (by decide) h10
          exact four 0 7 9 11 h0 h7 h9 h11 (by decide) (by decide)
      · obtain ⟨h6, -⟩ := two 9 6 7 (by decide) (by decide) h9
        by_cases h10 : (10 : Fin 12) ∈ S
        · exact four 6 7 10 11 h6 h7 h10 h11 (by decide) (by decide)
        · obtain ⟨h0, -⟩ := two 10 0 11 (by decide) (by decide) h10
          exact four 0 6 7 11 h0 h6 h7 h11 (by decide) (by decide)
  have hdisj : Disjoint (S ∩ Q) (S ∩ R) :=
    disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right (by decide))
  have := card_le_card (union_subset (inter_subset_left : S ∩ Q ⊆ S)
    (inter_subset_left : S ∩ R ⊆ S))
  rw [card_union_of_disjoint hdisj] at this
  omega

/-- **WOWII Conjecture 394 is false.** -/
theorem not_conjecture394 : ¬ Conjecture394 := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [G_A2, G_minLamSet] at h1
  have := G_matchingNumber
  have := G_twoDomNum
  omega

end WOWII394
