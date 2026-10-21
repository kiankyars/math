import OpenProblem.WOWII382b
import OpenProblem.WOWII378

/-!
# Written on the Wall II, Conjecture 401b is false

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 401b.** Let `G` be a connected graph on `n > 2` vertices. Then
> `γ_2 ≤ FLOOR[3*Tdist_max / freq[T_max(v)]]`.

Here `γ_2` is the 2-domination number and `Tdist(v) = ∑_u d(v, u)`. `freq[T_max(v)]` is the
number of vertices at which `T(v)` is maximal. We consider both natural readings of `T(v)`: the
number of triangles at `v`, and the total distance `Tdist(v)`.

Every star `K_{1,k}` with `k ≥ 6` is a counterexample under both readings. Each leaf must lie in
a 2-dominating set, so `γ_2 = k`. On the other hand `Tdist_max = 2k - 1`, attained at the leaves,
and the frequency is `k + 1` (no vertex lies in a triangle) or `k` (total distance). So the
bound is at most `⌊3(2k - 1)/k⌋ ≤ 5`. We formalize `K_{1,6}`.

Since the conjecture fails on such simple graphs, its transcription may be inaccurate.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII401b

open WOWII382b

variable {V : Type*} [Fintype V]

/-- The total distance of `v`. -/
def Tdist (G : SimpleGraph V) (v : V) : ℕ := ∑ u, G.dist v u

/-- The number of triangles at `v`. -/
def numTri (G : SimpleGraph V) (v : V) : ℕ :=
  #((G.neighborFinset v).powersetCard 2 |>.filter fun s => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b)

/-- The number of vertices at which `f` is maximal. -/
def freqMax (f : V → ℕ) : ℕ := #(univ.filter fun v => f v = univ.sup f)

/-- The statement of Conjecture 401b, for a reading `T` of `T(v)`. -/
def Conjecture401b (T : ∀ {V : Type} [Fintype V], SimpleGraph V → V → ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ 3 * univ.sup (Tdist G) / freqMax (T G)

/-! ### The star `K_{1,6}` -/

/-- The star with centre `0` and leaves `1, …, 6`. -/
def star : SimpleGraph (Fin 7) where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1⟩

lemma star_adj {a b : Fin 7} : star.Adj a b ↔ (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0) := Iff.rfl

lemma star_connected : star.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw]
  · exact (show star.Adj 0 w from Or.inl ⟨rfl, hw⟩).reachable

lemma star_dist (v w : Fin 7) :
    star.dist v w = if v = w then 0 else if v = 0 ∨ w = 0 then 1 else 2 := by
  by_cases hvw : v = w
  · simp [hvw]
  by_cases h0 : v = 0 ∨ w = 0
  · simp only [hvw, h0, ite_false, ite_true]
    apply dist_eq_one_iff_adj.mpr
    rcases h0 with rfl | rfl
    · exact Or.inl ⟨rfl, Ne.symm hvw⟩
    · exact Or.inr ⟨rfl, hvw⟩
  · simp only [hvw, h0, ite_false]
    push Not at h0
    apply le_antisymm
    · have h1 : star.Adj v 0 := Or.inr ⟨rfl, h0.1⟩
      have h2 : star.Adj 0 w := Or.inl ⟨rfl, h0.2⟩
      exact (dist_le (h1.toWalk.append h2.toWalk)).trans (by simp)
    · apply WOWII378.two_le_dist (star_connected.preconnected v w) hvw
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact h0.1 h
      · exact h0.2 h

lemma star_Tdist (v : Fin 7) : Tdist star v = if v = 0 then 6 else 11 := by
  rw [Tdist, Finset.sum_congr rfl fun w _ => star_dist v w]
  revert v
  decide

lemma star_sup_Tdist : univ.sup (Tdist star) = 11 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    rw [star_Tdist]
    split_ifs <;> omega
  · have := Finset.le_sup (f := Tdist star) (mem_univ 1)
    rwa [star_Tdist] at this

lemma star_freq_Tdist : freqMax (Tdist star) = 6 := by
  rw [freqMax, star_sup_Tdist]
  simp_rw [star_Tdist]
  decide

lemma star_numTri (v : Fin 7) : numTri star v = 0 := by
  rw [numTri, card_eq_zero, eq_empty_iff_forall_notMem]
  intro s hs
  simp only [mem_filter] at hs
  obtain ⟨hs, hcl⟩ := hs
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hcard
  have ha := (mem_neighborFinset _ _ _).mp (hsub (mem_insert_self a {b}))
  have hb := (mem_neighborFinset _ _ _).mp (hsub (mem_insert_of_mem (mem_singleton_self b)))
  have hadj := hcl a (mem_insert_self a {b}) b (mem_insert_of_mem (mem_singleton_self b)) hab
  rw [star_adj] at ha hb hadj
  omega

lemma star_freq_numTri : freqMax (numTri star) = 7 := by
  have : univ.sup (numTri star) = 0 := by
    apply le_antisymm (Finset.sup_le fun v _ => (star_numTri v).le) (Nat.zero_le _)
  rw [freqMax, this]
  simp [star_numTri]

/-- Every 2-dominating set of the star contains all six leaves. -/
lemma star_twoDomNum : 6 ≤ twoDomNum star := by
  have hne : {k | ∃ S, IsTwoDom star S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  rw [twoDomNum, ← hcard]
  have hleaf : ∀ v : Fin 7, v ≠ 0 → v ∈ S := by
    intro v hv
    by_contra hvS
    have h2 := hS v hvS
    have hsub : S.filter (star.Adj v) ⊆ {0} := by
      intro w hw
      have := (mem_filter.mp hw).2
      rw [star_adj] at this
      rcases this with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hv
      · exact mem_singleton.mpr h
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  have hsub : (univ.erase (0 : Fin 7)) ⊆ S := fun v hv => hleaf v (mem_erase.mp hv).1
  have := card_le_card hsub
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
  omega

/-- **WOWII Conjecture 401b is false** when `T(v)` is the total distance. -/
theorem not_conjecture401b_Tdist : ¬ Conjecture401b (fun G v => Tdist G v) := by
  intro h
  have h1 := h (Fin 7) star star_connected (by simp)
  rw [star_sup_Tdist, show freqMax (fun v => Tdist star v) = 6 from star_freq_Tdist] at h1
  have := star_twoDomNum
  omega

/-- **WOWII Conjecture 401b is false** when `T(v)` is the number of triangles at `v`. -/
theorem not_conjecture401b_numTri : ¬ Conjecture401b (fun G v => numTri G v) := by
  intro h
  have h1 := h (Fin 7) star star_connected (by simp)
  rw [star_sup_Tdist, show freqMax (fun v => numTri star v) = 7 from star_freq_numTri] at h1
  have := star_twoDomNum
  omega

end WOWII401b
