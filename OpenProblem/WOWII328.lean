import OpenProblem.WOWII326
import OpenProblem.WOWII444

/-!
# Written on the Wall II, Conjecture 328 is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 328.** Let `G` be a simple connected graph with `n > 1`. If
> `4 μ(Ḡ) ≤` frequency of `max {K(v)}`, where `K(v)` is the number of `K_4` incident to `v`,
> then `G` is well totally dominated.

Here `μ` is the matching number, the frequency of the maximum is the number of vertices `v` at
which `K(v)` is largest, and `G` is *well totally dominated* if all minimal total dominating sets
have the same size.

The counterexample `G` has 10 vertices and was found by simulated annealing. Vertices `0, …, 7`
form a `K_8`, and the path `8 - 9` is attached by the edges `1 - 8`, `4 - 8`, `2 - 9` and `6 - 9`.
An exhaustive search shows that no connected graph on at most 9 vertices is a counterexample.

* Every edge of `Ḡ` contains `8` or `9`, so `μ(Ḡ) ≤ 2`.
* Each vertex of the `K_8` lies in `35` copies of `K_4`, and `8` and `9` lie in none, so the
  maximum is attained `8 ≥ 4 μ(Ḡ)` times.
* `{1, 8}` and `{0, 3, 8, 9}` are both minimal total dominating sets.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII328

open WOWII372 WOWII326 WOWII444

variable {V : Type*} [Fintype V]

/-- The number of vertices at which the `K_4` count `numK4` is largest. -/
def freqMaxK4 (G : SimpleGraph V) : ℕ := #(univ.filter fun v => numK4 G v = univ.sup (numK4 G))

/-- The statement of Conjecture 328. -/
def Conjecture328 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 1 < Fintype.card V →
    4 * matchingNumber Gᶜ ≤ freqMaxK4 G → WellTotallyDominated G

omit [Fintype V] in
/-- A total dominating set is minimal once no single vertex can be removed. -/
lemma isMinTDS_of [DecidableEq V] {G : SimpleGraph V} {S : Finset V} (hS : IsTDS G S)
    (h : ∀ x ∈ S, ¬ IsTDS G (S.erase x)) : IsMinTDS G S := by
  refine ⟨hS, fun T hT hTt => ?_⟩
  obtain ⟨x, hxS, hxT⟩ := exists_of_ssubset hT
  apply h x hxS
  intro v
  obtain ⟨u, hu, hvu⟩ := hTt v
  exact ⟨u, mem_erase.mpr ⟨fun h => hxT (h ▸ hu), hT.1 hu⟩, hvu⟩

/-- The edges of a matching are edges of the graph. -/
lemma mem_edgeSet_of_isMatching {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    {e : Sym2 V} (he : e ∈ M) : e ∈ G.edgeSet :=
  mem_edgeFinset.mp (hM.1 he)

/-! ### The counterexample -/

def E : List (Fin 10 × Fin 10) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9), (3, 4), (3, 5),
    (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (6, 7), (6, 9), (8, 9)]

def adjB (a b : Fin 10) : Bool := E.contains (a, b) || E.contains (b, a)

def G : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun a b => adjB a b = true

lemma G_adj {a b : Fin 10} : G.Adj a b ↔ adjB a b = true := by
  have h : ∀ a b : Fin 10, (a ≠ b ∧ (adjB a b = true ∨ adjB b a = true)) ↔ adjB a b = true := by
    decide
  simpa [G] using h a b

lemma G_connected : G.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw]
  by_cases h1 : adjB 0 w = true
  · exact (G_adj.mpr h1).reachable
  · have : ∃ u, adjB 0 u = true ∧ adjB u w = true := by revert w; decide
    obtain ⟨u, hu, huw⟩ := this
    exact (G_adj.mpr hu).reachable.trans (G_adj.mpr huw).reachable

/-- Every edge of `Ḡ` contains `8` or `9`, so `μ(Ḡ) ≤ 2`. -/
lemma G_matching : matchingNumber Gᶜ ≤ 2 := by
  obtain ⟨M, hM, hcard⟩ := exists_max_matching Gᶜ
  rw [← hcard]
  have hcov : ∀ e ∈ M, (8 : Fin 10) ∈ e ∨ (9 : Fin 10) ∈ e := by
    intro e he
    have heG := mem_edgeSet_of_isMatching hM he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet, compl_adj, G_adj] at heG
      have key : ∀ a b : Fin 10,
          adjB a b = true ∨ a = b ∨ a = 8 ∨ a = 9 ∨ b = 8 ∨ b = 9 := by decide
      rcases key a b with h | h | h | h | h | h
      · exact absurd h heG.2
      · exact absurd h heG.1
      all_goals simp [h]
  have h1 : ∀ w, #(M.filter fun e => w ∈ e) ≤ 1 := by
    intro w
    rw [card_le_one]
    intro e he f hf
    by_contra hef
    exact hM.2 e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hef w (mem_filter.mp he).2
      (mem_filter.mp hf).2
  have hsub : M ⊆ (M.filter fun e => (8 : Fin 10) ∈ e) ∪ M.filter fun e => (9 : Fin 10) ∈ e := by
    intro e he
    rcases hcov e he with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨he, h⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  have := h1 8
  have := h1 9
  omega

/-- The `K_4` count from the Boolean adjacency. -/
def numK4B (v : Fin 10) : ℕ :=
  #((univ.filter fun w => adjB v w = true).powersetCard 3 |>.filter fun s =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → adjB a b = true)

lemma numK4_eq (v : Fin 10) : numK4 G v = numK4B v := by
  have hN : G.neighborFinset v = univ.filter fun w => adjB v w = true := by
    ext w
    simp [G_adj]
  rw [numK4, numK4B, hN]
  congr 1
  ext s
  simp only [mem_filter, G_adj]

/-- The maximum `K_4` count `35` is attained at the `8` vertices of the `K_8`. -/
lemma G_freq : freqMaxK4 G = 8 := by
  rw [freqMaxK4, show numK4 G = numK4B from funext numK4_eq]
  have hsup : univ.sup numK4B = 35 := by decide
  rw [hsup]
  decide

/-! ### Two minimal total dominating sets of different sizes -/

lemma not_tds_of {S : Finset (Fin 10)} (v : Fin 10) (h : ∀ u ∈ S, adjB v u = false) :
    ¬ IsTDS G S := by
  intro hS
  obtain ⟨u, hu, hvu⟩ := hS v
  rw [G_adj, h u hu] at hvu
  exact Bool.false_ne_true hvu

lemma G_min2 : IsMinTDS G {1, 8} := by
  refine isMinTDS_of (fun v => ?_) fun x hx => ?_
  · have key : ∀ v : Fin 10, adjB v 1 = true ∨ adjB v 8 = true := by decide
    rcases key v with h | h
    · exact ⟨1, by simp, G_adj.mpr h⟩
    · exact ⟨8, by simp, G_adj.mpr h⟩
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact not_tds_of 0 (by decide)
    · exact not_tds_of 1 (by decide)

lemma G_min4 : IsMinTDS G {0, 3, 8, 9} := by
  refine isMinTDS_of (fun v => ?_) fun x hx => ?_
  · have key : ∀ v : Fin 10,
        adjB v 0 = true ∨ adjB v 3 = true ∨ adjB v 8 = true ∨ adjB v 9 = true := by decide
    rcases key v with h | h | h | h
    · exact ⟨0, by simp, G_adj.mpr h⟩
    · exact ⟨3, by simp, G_adj.mpr h⟩
    · exact ⟨8, by simp, G_adj.mpr h⟩
    · exact ⟨9, by simp, G_adj.mpr h⟩
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact not_tds_of 3 (by decide)
    · exact not_tds_of 0 (by decide)
    · exact not_tds_of 9 (by decide)
    · exact not_tds_of 8 (by decide)

/-- **WOWII Conjecture 328 is false.** -/
theorem not_conjecture328 : ¬ Conjecture328 := by
  intro h
  have hW := h (Fin 10) G G_connected (by simp) (by rw [G_freq]; have := G_matching; omega)
  have := hW _ _ G_min2 G_min4
  simp at this

end WOWII328
