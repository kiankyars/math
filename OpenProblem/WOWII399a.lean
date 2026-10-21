import OpenProblem.WOWII382b
import OpenProblem.WOWII399b

/-!
# Written on the Wall II, Conjecture 399a is false as stated

E. DeLaViña's *Written on the Wall II* lists as open, with partial results:

> **Conjecture 399a.** If `G` is a connected graph on `n > 2` vertices, then
> `γ_2 ≤ WP(Ḡ) + ⌊α(G[C])/2⌋`, where `C` is the center.

Here `γ_2` is the 2-domination number, `WP` the Welsh–Powell number and `α` the independence
number. The WOWII note says that, since `γ_2 ≤ α_2 ≤ WP(Ḡ) + 1`, "it simply remains to settle
`γ_2 ≤ WP(Ḡ)` whenever `α(G[C]) = 1`".

That remaining case fails for every complete graph `K_n` with `n ≥ 3`: `γ_2(K_n) = 2`, while
`WP(K̄_n) = 1` and `α(K_n) = 1`. We record the triangle (`not_conjecture399a`). Graffiti.pc
checked its conjectures against a database that surely contains complete graphs, so this points
to a transcription problem, as for 382b.
-/

open Finset SimpleGraph

open scoped Classical

noncomputable section

namespace WOWII399a

open WOWII382b WOWII399b

variable {V : Type*} [Fintype V]

/-- The center: the vertices of minimum eccentricity. -/
def center (G : SimpleGraph V) : Finset V := univ.filter fun v => ∀ w, G.eccent v ≤ G.eccent w

/-- The statement of Conjecture 399a. -/
def Conjecture399a : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    twoDomNum G ≤ WP Gᶜ + alphaIn G (center G) / 2

/-- The complement of the triangle has no edges, so `WP(K̄_3) ≤ 1`. -/
lemma K3_WP : WP K3ᶜ ≤ 1 := by
  refine csSup_le ⟨0, by simp⟩ fun k hk => ?_
  have hk' := hk
  simp only [Set.mem_ofPred_eq] at hk'
  by_contra hlt
  push Not at hlt
  refine absurd (hk'.trans (card_le_card (t := ∅) fun v hv => ?_)) (by simp; omega)
  simp only [mem_filter, mem_univ, true_and] at hv
  rw [degree_eq_card_filter] at hv
  refine absurd (hv.trans (Nat.add_le_add_right
    (card_le_card (t := (∅ : Finset (Fin 3))) fun w hw => ?_) 1)) (by simp; omega)
  simp only [mem_filter, mem_univ, true_and, compl_adj, K3_adj] at hw
  exact absurd hw.1 (by simpa using hw.2)

/-- Every independent set of the triangle has at most one vertex. -/
lemma K3_alphaIn (A : Finset (Fin 3)) : alphaIn K3 A ≤ 1 := by
  refine csSup_le ⟨0, ∅, empty_subset _, fun x hx => absurd hx (notMem_empty x), rfl⟩ ?_
  rintro k ⟨S, -, hS, rfl⟩
  rw [card_le_one]
  intro a ha b hb
  by_contra hab
  exact hS a ha b hb hab

/-- **WOWII Conjecture 399a is false as stated**: the triangle is a counterexample. -/
theorem not_conjecture399a : ¬ Conjecture399a := by
  intro h
  have h1 := h (Fin 3) K3 K3_connected (by simp)
  have := K3_WP
  have := K3_alphaIn (center K3)
  have := K3_twoDomNum
  omega

end WOWII399a
