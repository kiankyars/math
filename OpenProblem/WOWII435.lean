import OpenProblem.WOWII434
import OpenProblem.WOWII449

/-!
# Written on the Wall II, Conjecture 435

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 435.** Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ SW(Ḡ) + ⌈(1 + |E(G²[A])|)/3⌉`, where `SW(Ḡ)` is the Szekeres–Wilf invariant of the
> complement of `G` and `E(G²[A])` is the edge set of the subgraph of `G²` induced by its minimum
> degree vertices.

Here `α_2` is the 2-independence number, the largest size of a set inducing a subgraph of maximum
degree at most one, and `SW(H) = 1 + max_X δ(H[X])`.

We prove the conjecture for every finite graph (`conjecture435`). The source's brackets are
unbalanced, so we also prove the reading `⌈1 + |E(G²[A])|/3⌉` (`conjecture435'`). Both follow
from `α_2(G) ≤ SW(Ḡ) + 1` (`twoIndepNum_le_SW`), because the ceiling is at least `1` in either
reading.

* Let `S` be a 2-independent set. Each `x ∈ S` has at most one neighbour in `S`, so in `Ḡ` it is
  adjacent to all but at most one of the other vertices of `S`.
* Hence `δ(Ḡ[S]) ≥ |S| - 2`, and `SW(Ḡ) ≥ 1 + (|S| - 2)`.

This is the Szekeres–Wilf analogue of the bound `α_k ≤ WP(Ḡ) + k - 1` of DeLaViña and Pepper.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII435

open WOWII434 WOWII449

variable {V : Type*} [Fintype V]

/-- Adjacency in the square `G²`: distinct vertices at distance at most two. -/
def sqAdj (G : SimpleGraph V) (v w : V) : Prop :=
  v ≠ w ∧ (G.Adj v w ∨ ∃ u, G.Adj v u ∧ G.Adj u w)

/-- The degree of `v` in `G²`. -/
def sqDeg (G : SimpleGraph V) (v : V) : ℕ := #(univ.filter (sqAdj G v))

/-- The vertices of minimum degree in `G²`. -/
def sqMinDegSet (G : SimpleGraph V) : Finset V := univ.filter fun v => ∀ w, sqDeg G v ≤ sqDeg G w

/-- The number of edges of `G²[A]`. -/
def sqEdgesIn (G : SimpleGraph V) (A : Finset V) : ℕ :=
  #(A.powersetCard 2 |>.filter fun s => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → sqAdj G a b)

/-- The statement of Conjecture 435. -/
def Conjecture435 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    (twoIndepNum G : ℤ) ≤ SW Gᶜ + ⌈((1 + sqEdgesIn G (sqMinDegSet G) : ℕ) : ℚ) / 3⌉

/-- The other reading of Conjecture 435. -/
def Conjecture435' : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 < Fintype.card V →
    (twoIndepNum G : ℤ) ≤ SW Gᶜ + ⌈1 + (sqEdgesIn G (sqMinDegSet G) : ℚ) / 3⌉

/-- `α_2(G) ≤ SW(Ḡ) + 1`. -/
theorem twoIndepNum_le_SW (G : SimpleGraph V) : twoIndepNum G ≤ SW Gᶜ + 1 := by
  obtain ⟨S, hS, hcard⟩ := exists_twoIndep G
  rw [← hcard]
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have := le_SW_of Gᶜ S hne (#S - 2) fun x hx => by
    have h1 := hS x hx
    have h3 : #(S.erase x) - #(S.filter (G.Adj x)) ≤ #((S.erase x) \ S.filter (G.Adj x)) :=
      le_card_sdiff _ _
    rw [card_erase_of_mem hx] at h3
    refine le_trans ?_ (card_le_card (s := (S.erase x) \ S.filter (G.Adj x)) fun y hy => ?_)
    · omega
    · simp only [mem_sdiff, mem_erase, mem_filter, not_and] at hy
      simp only [mem_filter, compl_adj]
      exact ⟨hy.1.2, Ne.symm hy.1.1, hy.2 hy.1.2⟩
  omega

/-- **WOWII Conjecture 435.** -/
theorem conjecture435 : Conjecture435 := by
  intro V _ G _ _
  have h := twoIndepNum_le_SW G
  have hc : (1 : ℤ) ≤ ⌈((1 + sqEdgesIn G (sqMinDegSet G) : ℕ) : ℚ) / 3⌉ := by
    rw [Int.one_le_ceil_iff]
    positivity
  omega

/-- **WOWII Conjecture 435**, with the ceiling read as `⌈1 + |E(G²[A])|/3⌉`. -/
theorem conjecture435' : Conjecture435' := by
  intro V _ G _ _
  have h := twoIndepNum_le_SW G
  have hc : (1 : ℤ) ≤ ⌈1 + (sqEdgesIn G (sqMinDegSet G) : ℚ) / 3⌉ := by
    rw [Int.one_le_ceil_iff]
    positivity
  omega

end WOWII435
