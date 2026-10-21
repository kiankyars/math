import Mathlib

/-!
# Written on the Wall II, Conjecture 372

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 372.** If `T` is a tree on `n > 2` vertices, then `γ_t(T) ≥ v_c(T) / (p(T) - 1)`.

Here `γ_t` is the total domination number, `v_c` the vertex cover number and `p` the path
covering number (the least number of vertex-disjoint paths covering all vertices). For a path
`p(T) = 1` and the right side is a division by zero, so the content of the conjecture is the
inequality `v_c(T) ≤ (p(T) - 1) γ_t(T)` for trees with `p(T) ≥ 2` (`conjecture372`); the
real-valued form with the convention `x / 0 = 0` is `conjecture372_real`.

The page notes that the case `p(T) ≥ 3` follows from `γ_t(T) ≥ (2/3)(v_c(T) + 1)`. We give a
self-contained proof of that bound by counting edges: a tree has `n - 1` edges, at least
`n - |S|` of them join a total dominating set `S` to its complement and at least `|S|/2` lie
inside `S`, so at most `|S|/2 - 1` edges avoid `S`, and `S` together with one end of each such
edge covers every edge.

The remaining case `p(T) = 2` is new. Such a tree consists of two vertex-disjoint paths
`P = f 0, …, f (a-1)` and `Q = g 0, …, g (b-1)` joined by a single edge `f i — g j`. A
parity class of `P` and one of `Q` (plus possibly one vertex) give a vertex cover of size
`⌊a/2⌋ + ⌊b/2⌋ + [a, b odd, i, j even]`, and a counting argument (every vertex of a path has at
most two neighbours on it) shows that every total dominating set is at least that large.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII372

variable {V : Type*} [Fintype V]

open SimpleGraph

/-! ### The invariants -/

/-- `S` is a total dominating set: every vertex has a neighbour in `S`. -/
def IsTDS (G : SimpleGraph V) (S : Finset V) : Prop := ∀ v, ∃ u ∈ S, G.Adj v u

/-- The total domination number `γ_t(G)`. -/
def totalDomNum (G : SimpleGraph V) : ℕ := sInf {k | ∃ S, IsTDS G S ∧ #S = k}

/-- `C` is a vertex cover: every edge has an end in `C`. -/
def IsVC (G : SimpleGraph V) (C : Finset V) : Prop := ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C

/-- The vertex cover number `v_c(G)`. -/
def vertexCoverNum (G : SimpleGraph V) : ℕ := sInf {k | ∃ C, IsVC G C ∧ #C = k}

/-- A family of vertex-disjoint paths covering all vertices (as in formal-conjectures). -/
def IsPathCover (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- The path covering number `p(G)`. -/
def pathCoverNumber (G : SimpleGraph V) : ℕ := sInf {k | ∃ P, #P = k ∧ IsPathCover G P}

omit [Fintype V] in
lemma vertexCoverNum_le {G : SimpleGraph V} {C : Finset V} (hC : IsVC G C) :
    vertexCoverNum G ≤ #C :=
  Nat.sInf_le ⟨C, hC, rfl⟩

lemma exists_tds_card_eq {G : SimpleGraph V} (hG : ∀ v, ∃ u, G.Adj v u) :
    ∃ S, IsTDS G S ∧ #S = totalDomNum G := by
  have hne : {k | ∃ S, IsTDS G S ∧ #S = k}.Nonempty :=
    ⟨_, univ, fun v => by obtain ⟨u, hu⟩ := hG v; exact ⟨u, mem_univ u, hu⟩, rfl⟩
  exact Nat.sInf_mem hne

lemma exists_pathCover_card_eq (G : SimpleGraph V) :
    ∃ P, #P = pathCoverNumber G ∧ IsPathCover G P := by
  have hne : {k | ∃ P, #P = k ∧ IsPathCover G P}.Nonempty := by
    refine ⟨_, univ.image (fun v => ({v} : Finset V)), rfl, ?_, ?_, ?_⟩
    · intro s1 h1 s2 h2 hne
      obtain ⟨v, -, rfl⟩ := mem_image.mp h1
      obtain ⟨w, -, rfl⟩ := mem_image.mp h2
      rw [Finset.disjoint_singleton]
      rintro rfl
      exact hne rfl
    · intro v _
      exact mem_biUnion.mpr ⟨{v}, mem_image.mpr ⟨v, mem_univ v, rfl⟩, mem_singleton_self v⟩
    · intro s hs
      obtain ⟨v, -, rfl⟩ := mem_image.mp hs
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  exact Nat.sInf_mem hne

/-! ### The case `p ≥ 3`: an edge count -/

/-- `e` has both ends in `S`. -/
def BothIn (S : Finset V) (e : Sym2 V) : Prop := ∀ v ∈ e, v ∈ S

/-- `e` has no end in `S`. -/
def NoneIn (S : Finset V) (e : Sym2 V) : Prop := ∀ v ∈ e, v ∉ S

/-- In a tree, at most `|S|/2 - 1` edges avoid a total dominating set `S`. -/
lemma card_noneIn_le {T : SimpleGraph V} (hT : T.IsTree) {S : Finset V} (hS : IsTDS T S) :
    2 * #(T.edgeFinset.filter (NoneIn S)) + 2 ≤ #S := by
  let E := T.edgeFinset
  let Ein := E.filter (BothIn S)
  let Erest := E.filter (fun e => ¬ BothIn S e)
  let Eout := Erest.filter (NoneIn S)
  let Ebt := Erest.filter (fun e => ¬ NoneIn S e)
  have h1 : #Ein + #Erest = #E := Finset.card_filter_add_card_filter_not _
  have h2 : #Eout + #Ebt = #Erest := Finset.card_filter_add_card_filter_not _
  have hcardE : #E + 1 = Fintype.card V := hT.card_edgeFinset
  -- each vertex outside `S` gives an edge to `S`
  choose σ hσS hσ using hS
  have hbt : Fintype.card V - #S ≤ #Ebt := by
    have : #(Sᶜ) ≤ #Ebt := by
      apply Finset.card_le_card_of_injOn (fun v => s(v, σ v))
      · intro v hv
        have hvS : v ∉ S := Finset.mem_compl.mp hv
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨T.mem_edgeFinset.mpr (hσ v),
          fun h => hvS (h v (Sym2.mem_mk_left _ _))⟩,
          fun h => h (σ v) (Sym2.mem_mk_right _ _) (hσS v)⟩
      · intro v hv w hw hvw
        have hvS : v ∉ S := Finset.mem_compl.mp hv
        rcases Sym2.eq_iff.mp hvw with ⟨h, -⟩ | ⟨h1, -⟩
        · exact h
        · exact absurd (h1 ▸ hσS w) hvS
    rw [Finset.card_compl] at this
    exact this
  -- each vertex of `S` gives an edge inside `S`; each edge is hit at most twice
  have hin : #S ≤ 2 * #Ein := by
    have hmap : ∀ v ∈ S, s(v, σ v) ∈ Ein := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨T.mem_edgeFinset.mpr (hσ v), fun w hw => ?_⟩
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hv
      · exact hσS v
    calc #S ≤ 2 * #(S.image fun v => s(v, σ v)) := by
          apply Finset.card_le_mul_card_image
          intro e _
          induction e using Sym2.ind with
          | h x y =>
            calc #{v ∈ S | s(v, σ v) = s(x, y)} ≤ #({x, y} : Finset V) := by
                  apply Finset.card_le_card
                  intro v hv
                  rw [Finset.mem_filter] at hv
                  have := hv.2 ▸ Sym2.mem_mk_left v (σ v)
                  rcases Sym2.mem_iff.mp this with rfl | rfl <;> simp
              _ ≤ 2 := Finset.card_le_two
      _ ≤ 2 * #Ein := by
          gcongr
          intro e he
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
          exact hmap v hv
  have hEout : Eout = T.edgeFinset.filter (NoneIn S) := by
    ext e
    simp only [Eout, Erest, E, Finset.mem_filter]
    constructor
    · rintro ⟨⟨he, -⟩, hn⟩
      exact ⟨he, hn⟩
    · rintro ⟨he, hn⟩
      exact ⟨⟨he, fun hb => hn _ (Sym2.out_fst_mem e) (hb _ (Sym2.out_fst_mem e))⟩, hn⟩
  rw [← hEout]
  omega

/-- In a tree, a total dominating set `S` yields a vertex cover `C` with
`2|C| + 2 ≤ 3|S|`. -/
lemma exists_vc_of_tds {T : SimpleGraph V} (hT : T.IsTree) {S : Finset V} (hS : IsTDS T S) :
    ∃ C, IsVC T C ∧ 2 * #C + 2 ≤ 3 * #S := by
  let Eout := T.edgeFinset.filter (NoneIn S)
  have hcount : 2 * #Eout + 2 ≤ #S := card_noneIn_le hT hS
  -- the cover: `S` together with one end of each edge avoiding `S`
  refine ⟨S ∪ Eout.image (fun e => e.out.1), ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ S
    · exact Or.inl (Finset.mem_union_left _ hu)
    by_cases hv : v ∈ S
    · exact Or.inr (Finset.mem_union_left _ hv)
    have hnone : NoneIn S s(u, v) := by
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact hv
    have he : s(u, v) ∈ Eout := Finset.mem_filter.mpr ⟨T.mem_edgeFinset.mpr huv, hnone⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u, v)) with h | h
    · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, he, h⟩))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, he, h⟩))
  · have := Finset.card_union_le S (Eout.image (fun e => e.out.1))
    have := Finset.card_image_le (s := Eout) (f := fun e => e.out.1)
    omega

/-! ### The case `p = 2`: two paths joined by an edge -/

/-- Two vertex-disjoint paths `f 0, …, f (a-1)` and `g 0, …, g (b-1)` covering the vertices,
whose edges together with the single edge `f i — g j` are exactly the edges of `T`. -/
structure TwoPaths (T : SimpleGraph V) where
  a : ℕ
  b : ℕ
  f : ℕ → V
  g : ℕ → V
  i : ℕ
  j : ℕ
  hi : i < a
  hj : j < b
  f_inj : ∀ k m, k < a → m < a → f k = f m → k = m
  g_inj : ∀ k m, k < b → m < b → g k = g m → k = m
  fg_ne : ∀ k m, k < a → m < b → f k ≠ g m
  adj_iff : ∀ u v, T.Adj u v ↔ (∃ k, k + 1 < a ∧ s(u, v) = s(f k, f (k + 1))) ∨
    (∃ k, k + 1 < b ∧ s(u, v) = s(g k, g (k + 1))) ∨ s(u, v) = s(f i, g j)

/-- If every `k ∈ U` has `k + 1` or `k - 1` in `E`, then `|U| ≤ 2|E|`. -/
lemma card_le_two_mul (U E : Finset ℕ) (h : ∀ k ∈ U, k + 1 ∈ E ∨ (1 ≤ k ∧ k - 1 ∈ E)) :
    #U ≤ 2 * #E := by
  have hsub : U ⊆ E.image (fun m => m - 1) ∪ E.image (fun m => m + 1) := by
    intro k hk
    rcases h k hk with h1 | ⟨h1, h2⟩
    · exact mem_union_left _ (mem_image.mpr ⟨k + 1, h1, by omega⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨k - 1, h2, by omega⟩)
  calc #U ≤ #(E.image (fun m => m - 1) ∪ E.image (fun m => m + 1)) := card_le_card hsub
    _ ≤ #(E.image (fun m => m - 1)) + #(E.image (fun m => m + 1)) := card_union_le _ _
    _ ≤ #E + #E := add_le_add card_image_le card_image_le
    _ = 2 * #E := by ring

lemma card_parity (a r : ℕ) (hr : r < 2) :
    #((range a).filter (fun k => k % 2 = r)) = (a + 1 - r) / 2 := by
  induction a with
  | zero => simp; omega
  | succ n ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]
      omega
    · rw [ih]
      omega

namespace TwoPaths

variable {T : SimpleGraph V} (H : TwoPaths T)

omit [Fintype V] in
lemma nbr_f {k : ℕ} (hk : k < H.a) {w : V} (h : T.Adj (H.f k) w) :
    (k + 1 < H.a ∧ w = H.f (k + 1)) ∨ (1 ≤ k ∧ w = H.f (k - 1)) ∨
      (k = H.i ∧ w = H.g H.j) := by
  rcases (H.adj_iff _ _).mp h with ⟨m, hm, he⟩ | ⟨m, hm, he⟩ | he
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := H.f_inj k m hk (by omega) h1
      subst this
      exact Or.inl ⟨hm, h2⟩
    · have := H.f_inj k (m + 1) hk hm h1
      subst this
      exact Or.inr (Or.inl ⟨by omega, by simpa using h2⟩)
  · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (H.fg_ne k m hk (by omega))
    · exact absurd h1 (H.fg_ne k (m + 1) hk hm)
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr (Or.inr ⟨H.f_inj k H.i hk H.hi h1, h2⟩)
    · exact absurd h1 (H.fg_ne k H.j hk H.hj)

omit [Fintype V] in
lemma nbr_g {k : ℕ} (hk : k < H.b) {w : V} (h : T.Adj (H.g k) w) :
    (k + 1 < H.b ∧ w = H.g (k + 1)) ∨ (1 ≤ k ∧ w = H.g (k - 1)) ∨
      (k = H.j ∧ w = H.f H.i) := by
  rcases (H.adj_iff _ _).mp h with ⟨m, hm, he⟩ | ⟨m, hm, he⟩ | he
  · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1.symm (H.fg_ne m k (by omega) hk)
    · exact absurd h1.symm (H.fg_ne (m + 1) k hm hk)
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := H.g_inj k m hk (by omega) h1
      subst this
      exact Or.inl ⟨hm, h2⟩
    · have := H.g_inj k (m + 1) hk hm h1
      subst this
      exact Or.inr (Or.inl ⟨by omega, by simpa using h2⟩)
  · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1.symm (H.fg_ne H.i k H.hi hk)
    · exact Or.inr (Or.inr ⟨H.g_inj k H.j hk H.hj h1, h2⟩)

/-- The size of the explicit vertex cover. -/
def vcBound : ℕ :=
  H.a / 2 + H.b / 2 + if H.a % 2 = 1 ∧ H.i % 2 = 0 ∧ H.b % 2 = 1 ∧ H.j % 2 = 0 then 1 else 0

omit [Fintype V] in
/-- Every total dominating set has at least `vcBound` vertices. -/
lemma vcBound_le {S : Finset V} (hS : IsTDS T S) : H.vcBound ≤ #S := by
  set D := (range H.a).filter (fun k => H.f k ∈ S) with hD
  set E := (range H.b).filter (fun k => H.g k ∈ S) with hE
  have memD : ∀ k, k ∈ D ↔ k < H.a ∧ H.f k ∈ S := by intro k; simp [hD]
  have memE : ∀ k, k ∈ E ↔ k < H.b ∧ H.g k ∈ S := by intro k; simp [hE]
  -- `|D| + |E| ≤ |S|`
  have hDE : #D + #E ≤ #S := by
    have hf : #(D.image H.f) = #D := by
      apply card_image_of_injOn
      intro k hk m hm h
      exact H.f_inj k m ((memD k).mp hk).1 ((memD m).mp hm).1 h
    have hg : #(E.image H.g) = #E := by
      apply card_image_of_injOn
      intro k hk m hm h
      exact H.g_inj k m ((memE k).mp hk).1 ((memE m).mp hm).1 h
    have hdisj : Disjoint (D.image H.f) (E.image H.g) := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
      obtain ⟨m, hm, h⟩ := mem_image.mp hv'
      exact H.fg_ne k m ((memD k).mp hk).1 ((memE m).mp hm).1 h.symm
    have hsub : D.image H.f ∪ E.image H.g ⊆ S := by
      intro v hv
      rcases mem_union.mp hv with hv | hv
      · obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
        exact ((memD k).mp hk).2
      · obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
        exact ((memE k).mp hk).2
    calc #D + #E = #(D.image H.f ∪ E.image H.g) := by
          rw [card_union_of_disjoint hdisj, hf, hg]
      _ ≤ #S := card_le_card hsub
  -- domination along the paths
  have domf : ∀ k < H.a, k ≠ H.i → k + 1 ∈ D ∨ (1 ≤ k ∧ k - 1 ∈ D) := by
    intro k hk hki
    obtain ⟨u, huS, hu⟩ := hS (H.f k)
    rcases H.nbr_f hk hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩
    · exact Or.inl ((memD _).mpr ⟨h1, huS⟩)
    · exact Or.inr ⟨h1, (memD _).mpr ⟨by omega, huS⟩⟩
    · exact absurd h1 hki
  have domfi : (H.i + 1 ∈ D ∨ (1 ≤ H.i ∧ H.i - 1 ∈ D)) ∨ H.j ∈ E := by
    obtain ⟨u, huS, hu⟩ := hS (H.f H.i)
    rcases H.nbr_f H.hi hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl (Or.inl ((memD _).mpr ⟨h1, huS⟩))
    · exact Or.inl (Or.inr ⟨h1, (memD _).mpr ⟨by have := H.hi; omega, huS⟩⟩)
    · exact Or.inr ((memE _).mpr ⟨H.hj, huS⟩)
  have domg : ∀ k < H.b, k ≠ H.j → k + 1 ∈ E ∨ (1 ≤ k ∧ k - 1 ∈ E) := by
    intro k hk hkj
    obtain ⟨u, huS, hu⟩ := hS (H.g k)
    rcases H.nbr_g hk hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩
    · exact Or.inl ((memE _).mpr ⟨h1, huS⟩)
    · exact Or.inr ⟨h1, (memE _).mpr ⟨by omega, huS⟩⟩
    · exact absurd h1 hkj
  have domgj : (H.j + 1 ∈ E ∨ (1 ≤ H.j ∧ H.j - 1 ∈ E)) ∨ H.i ∈ D := by
    obtain ⟨u, huS, hu⟩ := hS (H.g H.j)
    rcases H.nbr_g H.hj hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl (Or.inl ((memE _).mpr ⟨h1, huS⟩))
    · exact Or.inl (Or.inr ⟨h1, (memE _).mpr ⟨by have := H.hj; omega, huS⟩⟩)
    · exact Or.inr ((memD _).mpr ⟨H.hi, huS⟩)
  -- counting on `P`
  have hBf : H.a - 1 ≤ 2 * #D := by
    have := card_le_two_mul ((range H.a).erase H.i) D (fun k hk => by
      rw [mem_erase, mem_range] at hk
      exact domf k hk.2 hk.1)
    rwa [card_erase_of_mem (mem_range.mpr H.hi), card_range] at this
  have hAf : (H.i + 1 ∈ D ∨ (1 ≤ H.i ∧ H.i - 1 ∈ D)) → H.a ≤ 2 * #D := by
    intro hint
    have := card_le_two_mul (range H.a) D (fun k hk => by
      rw [mem_range] at hk
      by_cases hki : k = H.i
      · subst hki; exact hint
      · exact domf k hk hki)
    rwa [card_range] at this
  have hBg : H.b - 1 ≤ 2 * #E := by
    have := card_le_two_mul ((range H.b).erase H.j) E (fun k hk => by
      rw [mem_erase, mem_range] at hk
      exact domg k hk.2 hk.1)
    rwa [card_erase_of_mem (mem_range.mpr H.hj), card_range] at this
  have hAg : (H.j + 1 ∈ E ∨ (1 ≤ H.j ∧ H.j - 1 ∈ E)) → H.b ≤ 2 * #E := by
    intro hint
    have := card_le_two_mul (range H.b) E (fun k hk => by
      rw [mem_range] at hk
      by_cases hkj : k = H.j
      · subst hkj; exact hint
      · exact domg k hk hkj)
    rwa [card_range] at this
  -- if `f i` is dominated only by `g j`, then `D` is large on both sides of `i`
  have hCf : ¬ (H.i + 1 ∈ D ∨ (1 ≤ H.i ∧ H.i - 1 ∈ D)) → H.i ∈ D →
      H.a + 1 ≤ 2 * #D ∨ H.a % 2 = 0 ∨ H.i % 2 = 1 := by
    intro hnot hiD
    push Not at hnot
    obtain ⟨hnr, hnl⟩ := hnot
    set EL := D.filter (fun m => m + 2 ≤ H.i)
    set ER := D.filter (fun m => H.i + 2 ≤ m)
    have hL : H.i - 1 ≤ 2 * #EL := by
      have := card_le_two_mul (range (H.i - 1)) EL (fun k hk => by
        rw [mem_range] at hk
        rcases domf k (by have := H.hi; omega) (by omega) with h1 | ⟨h1, h2⟩
        · left
          refine mem_filter.mpr ⟨h1, ?_⟩
          by_contra hc
          exact hnl (by omega) (by rwa [show H.i - 1 = k + 1 by omega])
        · exact Or.inr ⟨h1, mem_filter.mpr ⟨h2, by omega⟩⟩)
      rwa [card_range] at this
    have hR : H.a - H.i - 2 ≤ 2 * #ER := by
      have := card_le_two_mul (Ico (H.i + 2) H.a) ER (fun k hk => by
        rw [mem_Ico] at hk
        rcases domf k hk.2 (by omega) with h1 | ⟨h1, h2⟩
        · exact Or.inl (mem_filter.mpr ⟨h1, by omega⟩)
        · right
          refine ⟨h1, mem_filter.mpr ⟨h2, ?_⟩⟩
          by_contra hc
          exact hnr (by rwa [show H.i + 1 = k - 1 by omega]))
      rwa [Nat.card_Ico] at this
    have hsum : #EL + #ER + 1 ≤ #D := by
      have hdisj : Disjoint EL ER := by
        rw [Finset.disjoint_left]
        intro m h1 h2
        have := (mem_filter.mp h1).2
        have := (mem_filter.mp h2).2
        omega
      have hiL : H.i ∉ EL ∪ ER := by
        intro h
        rcases mem_union.mp h with h | h <;> have := (mem_filter.mp h).2 <;> omega
      have hsub : insert H.i (EL ∪ ER) ⊆ D := by
        intro m hm
        rcases mem_insert.mp hm with rfl | hm
        · exact hiD
        · rcases mem_union.mp hm with h | h
          · exact (mem_filter.mp h).1
          · exact (mem_filter.mp h).1
      have := card_le_card hsub
      rw [card_insert_of_notMem hiL, card_union_of_disjoint hdisj] at this
      exact this
    have := H.hi
    omega
  -- the final count
  unfold vcBound
  have hi := H.hi
  have hj := H.hj
  by_cases hfi : H.i + 1 ∈ D ∨ (1 ≤ H.i ∧ H.i - 1 ∈ D)
  · have h1 := hAf hfi
    by_cases hgj : H.j + 1 ∈ E ∨ (1 ≤ H.j ∧ H.j - 1 ∈ E)
    · have h2 := hAg hgj
      split_ifs <;> omega
    · split_ifs <;> omega
  · have hjE : H.j ∈ E := domfi.resolve_left hfi
    by_cases hgj : H.j + 1 ∈ E ∨ (1 ≤ H.j ∧ H.j - 1 ∈ E)
    · have h2 := hAg hgj
      split_ifs <;> omega
    · have hiD : H.i ∈ D := domgj.resolve_left hgj
      have h3 := hCf hfi hiD
      split_ifs <;> omega

omit [Fintype V] in
/-- An explicit vertex cover with `vcBound` vertices. -/
lemma exists_vc : ∃ C, IsVC T C ∧ #C ≤ H.vcBound := by
  let cP : Prop := H.a % 2 = 0 ∨ H.i % 2 = 1
  let cQ : Prop := H.b % 2 = 0 ∨ H.j % 2 = 1
  let rP : ℕ := if cP then H.i % 2 else 1
  let rQ : ℕ := if cQ then H.j % 2 else 1
  let CP := (range H.a).filter (fun k => k % 2 = rP)
  let CQ := (range H.b).filter (fun k => k % 2 = rQ)
  let X : Finset V := if cP ∨ cQ then ∅ else {H.f H.i}
  have hrP : rP < 2 := by simp only [rP]; split_ifs <;> omega
  have hrQ : rQ < 2 := by simp only [rQ]; split_ifs <;> omega
  refine ⟨CP.image H.f ∪ CQ.image H.g ∪ X, ?_, ?_⟩
  · intro u v huv
    rcases (H.adj_iff u v).mp huv with ⟨k, hk, he⟩ | ⟨k, hk, he⟩ | he
    · have hcov : H.f k ∈ CP.image H.f ∪ CQ.image H.g ∪ X ∨
          H.f (k + 1) ∈ CP.image H.f ∪ CQ.image H.g ∪ X := by
        by_cases hpar : k % 2 = rP
        · exact Or.inl (mem_union_left _ (mem_union_left _
            (mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_range.mpr (by omega), hpar⟩, rfl⟩)))
        · exact Or.inr (mem_union_left _ (mem_union_left _
            (mem_image.mpr ⟨k + 1, mem_filter.mpr ⟨mem_range.mpr hk, by omega⟩, rfl⟩)))
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcov
      · exact hcov.symm
    · have hcov : H.g k ∈ CP.image H.f ∪ CQ.image H.g ∪ X ∨
          H.g (k + 1) ∈ CP.image H.f ∪ CQ.image H.g ∪ X := by
        by_cases hpar : k % 2 = rQ
        · exact Or.inl (mem_union_left _ (mem_union_right _
            (mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_range.mpr (by omega), hpar⟩, rfl⟩)))
        · exact Or.inr (mem_union_left _ (mem_union_right _
            (mem_image.mpr ⟨k + 1, mem_filter.mpr ⟨mem_range.mpr hk, by omega⟩, rfl⟩)))
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcov
      · exact hcov.symm
    · have hcov : H.f H.i ∈ CP.image H.f ∪ CQ.image H.g ∪ X ∨
          H.g H.j ∈ CP.image H.f ∪ CQ.image H.g ∪ X := by
        by_cases h1 : cP
        · refine Or.inl (mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨H.i,
            mem_filter.mpr ⟨mem_range.mpr H.hi, ?_⟩, rfl⟩)))
          simp [rP, h1]
        · by_cases h2 : cQ
          · refine Or.inr (mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨H.j,
              mem_filter.mpr ⟨mem_range.mpr H.hj, ?_⟩, rfl⟩)))
            simp [rQ, h2]
          · refine Or.inl (mem_union_right _ ?_)
            simp [X, h1, h2]
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcov
      · exact hcov.symm
  · have hCP : #CP ≤ H.a / 2 := by
      have := card_parity H.a rP hrP
      simp only [CP]
      rw [this]
      simp only [rP, cP]
      split_ifs <;> omega
    have hCQ : #CQ ≤ H.b / 2 := by
      have := card_parity H.b rQ hrQ
      simp only [CQ]
      rw [this]
      simp only [rQ, cQ]
      split_ifs <;> omega
    have hX : #X ≤ if H.a % 2 = 1 ∧ H.i % 2 = 0 ∧ H.b % 2 = 1 ∧ H.j % 2 = 0 then 1 else 0 := by
      simp only [X, cP, cQ]
      split_ifs <;> simp_all
    calc #(CP.image H.f ∪ CQ.image H.g ∪ X)
        ≤ #(CP.image H.f ∪ CQ.image H.g) + #X := card_union_le _ _
      _ ≤ #(CP.image H.f) + #(CQ.image H.g) + #X := by
          gcongr
          exact card_union_le _ _
      _ ≤ #CP + #CQ + #X := by
          gcongr
          · exact card_image_le
          · exact card_image_le
      _ ≤ H.vcBound := by
          unfold vcBound
          omega

omit [Fintype V] in
include H in
/-- For two paths joined by an edge, `v_c ≤ |S|` for every total dominating set `S`. -/
lemma vc_le_tds {S : Finset V} (hS : IsTDS T S) : vertexCoverNum T ≤ #S := by
  obtain ⟨C, hC, hcard⟩ := H.exists_vc
  exact (vertexCoverNum_le hC).trans (hcard.trans (H.vcBound_le hS))

end TwoPaths

/-! ### Trees with a cover by two paths -/

omit [Fintype V] in
lemma not_reachable_of_closed {K : SimpleGraph V} {x y : V} (C : Set V) (hx : x ∈ C)
    (hy : y ∉ C) (hC : ∀ u w, K.Adj u w → u ∈ C → w ∈ C) : ¬ K.Reachable x y := by
  rintro ⟨q⟩
  suffices ∀ {u w : V} (r : K.Walk u w), u ∈ C → w ∈ C from hy (this q hx)
  intro u w r
  induction r with
  | nil => exact id
  | cons h _ ih => exact fun hu => ih (hC _ _ h hu)

/-- A tree covered by two vertex-disjoint paths consists of the two paths and one more edge. -/
lemma exists_twoPaths {T : SimpleGraph V} (hT : T.IsTree) {P : Finset (Finset V)}
    (hP : IsPathCover T P) (hcard : #P = 2) : Nonempty (TwoPaths T) := by
  obtain ⟨W1, W2, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨hdisj, hcov, hpath⟩ := hP
  have hd : Disjoint W1 W2 := hdisj W1 (by simp) W2 (by simp) hne
  obtain ⟨u1, v1, p1, hp1, hW1⟩ := hpath W1 (by simp)
  obtain ⟨u2, v2, p2, hp2, hW2⟩ := hpath W2 (by simp)
  set f := p1.getVert with hf
  set g := p2.getVert with hg
  have f_mem : ∀ k, f k ∈ W1 := fun k => hW1 ▸ List.mem_toFinset.mpr (p1.getVert_mem_support k)
  have g_mem : ∀ k, g k ∈ W2 := fun k => hW2 ▸ List.mem_toFinset.mpr (p2.getVert_mem_support k)
  have f_inj : ∀ k m, k < p1.length + 1 → m < p1.length + 1 → f k = f m → k = m :=
    fun k m hk hm h => hp1.getVert_injOn (by simp only [Set.mem_ofPred]; omega)
      (by simp only [Set.mem_ofPred]; omega) h
  have g_inj : ∀ k m, k < p2.length + 1 → m < p2.length + 1 → g k = g m → k = m :=
    fun k m hk hm h => hp2.getVert_injOn (by simp only [Set.mem_ofPred]; omega)
      (by simp only [Set.mem_ofPred]; omega) h
  have fg_ne : ∀ k m, f k ≠ g m := fun k m h => disjoint_left.mp hd (f_mem k) (h ▸ g_mem m)
  have W1_cover : ∀ v ∈ W1, ∃ k < p1.length + 1, f k = v := by
    intro v hv
    rw [hW1, List.mem_toFinset] at hv
    obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    exact ⟨k, by omega, hk⟩
  have W2_cover : ∀ v ∈ W2, ∃ k < p2.length + 1, g k = v := by
    intro v hv
    rw [hW2, List.mem_toFinset] at hv
    obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    exact ⟨k, by omega, hk⟩
  have hmemW : ∀ v, v ∈ W1 ∨ v ∈ W2 := by
    intro v
    have := hcov (mem_univ v)
    simp only [mem_biUnion, mem_insert, mem_singleton, id] at this
    obtain ⟨w, hw, hvw⟩ := this
    rcases hw with rfl | rfl
    · exact Or.inl hvw
    · exact Or.inr hvw
  -- cardinalities
  have hW1card : #W1 = p1.length + 1 := by
    rw [hW1, List.toFinset_card_of_nodup hp1.support_nodup, Walk.length_support]
  have hW2card : #W2 = p2.length + 1 := by
    rw [hW2, List.toFinset_card_of_nodup hp2.support_nodup, Walk.length_support]
  have hVcard : Fintype.card V = (p1.length + 1) + (p2.length + 1) := by
    rw [← hW1card, ← hW2card, ← card_union_of_disjoint hd, ← card_univ]
    congr 1
    ext v
    simp only [mem_univ, mem_union, true_iff]
    exact hmemW v
  -- the path edges
  let EP := (range p1.length).image (fun k => s(f k, f (k + 1)))
  let EQ := (range p2.length).image (fun k => s(g k, g (k + 1)))
  have hEP : #EP = p1.length := by
    rw [card_image_of_injOn, card_range]
    intro k hk m hm h
    simp only [coe_range, Set.mem_Iio] at hk hm
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact f_inj k m (by omega) (by omega) h1
    · have := f_inj k (m + 1) (by omega) (by omega) h1
      have := f_inj (k + 1) m (by omega) (by omega) h2
      omega
  have hEQ : #EQ = p2.length := by
    rw [card_image_of_injOn, card_range]
    intro k hk m hm h
    simp only [coe_range, Set.mem_Iio] at hk hm
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact g_inj k m (by omega) (by omega) h1
    · have := g_inj k (m + 1) (by omega) (by omega) h1
      have := g_inj (k + 1) m (by omega) (by omega) h2
      omega
  have hsubP : EP ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := mem_image.mp he
    exact T.mem_edgeFinset.mpr (p1.adj_getVert_succ (mem_range.mp hk))
  have hsubQ : EQ ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := mem_image.mp he
    exact T.mem_edgeFinset.mpr (p2.adj_getVert_succ (mem_range.mp hk))
  have hdPQ : Disjoint EP EQ := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨m, -, h⟩ := mem_image.mp h2
    rcases Sym2.eq_iff.mp h with ⟨h3, -⟩ | ⟨h3, -⟩
    · exact fg_ne k m h3.symm
    · exact fg_ne (k + 1) m h3.symm
  have hE : #T.edgeFinset + 1 = Fintype.card V := hT.card_edgeFinset
  have hrest : #(T.edgeFinset \ (EP ∪ EQ)) = 1 := by
    rw [card_sdiff_of_subset (union_subset hsubP hsubQ), card_union_of_disjoint hdPQ]
    omega
  obtain ⟨e, he⟩ := card_eq_one.mp hrest
  have heE : e ∈ T.edgeFinset := (mem_sdiff.mp (he ▸ mem_singleton_self e)).1
  have hedges : ∀ e', e' ∈ T.edgeFinset ↔ e' ∈ EP ∨ e' ∈ EQ ∨ e' = e := by
    intro e'
    constructor
    · intro h
      by_cases h1 : e' ∈ EP ∪ EQ
      · rcases mem_union.mp h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
      · have : e' ∈ T.edgeFinset \ (EP ∪ EQ) := mem_sdiff.mpr ⟨h, h1⟩
        rw [he, mem_singleton] at this
        exact Or.inr (Or.inr this)
    · rintro (h | h | rfl)
      · exact hsubP h
      · exact hsubQ h
      · exact heE
  -- the extra edge joins the two paths
  induction e using Sym2.ind with
  | h x y =>
  have hxy : (x ∈ W1 ∧ y ∈ W2) ∨ (x ∈ W2 ∧ y ∈ W1) := by
    by_contra hcon
    have hside : (x ∈ W1 ↔ y ∈ W1) := by
      rcases hmemW x with hx | hx <;> rcases hmemW y with hy | hy
      · exact ⟨fun _ => hy, fun _ => hx⟩
      · exact absurd (Or.inl ⟨hx, hy⟩) hcon
      · exact absurd (Or.inr ⟨hx, hy⟩) hcon
      · exact ⟨fun h => absurd h (disjoint_left.mp hd.symm hx),
          fun h => absurd h (disjoint_left.mp hd.symm hy)⟩
    have hclosed : ∀ u w, T.Adj u w → u ∈ (W1 : Set V) → w ∈ (W1 : Set V) := by
      intro u w huw hu
      rw [Finset.mem_coe] at hu ⊢
      rcases (hedges s(u, w)).mp (T.mem_edgeFinset.mpr huw) with h | h | h
      · obtain ⟨k, -, hk⟩ := mem_image.mp h
        rcases Sym2.eq_iff.mp hk with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · exact f_mem _
        · exact f_mem _
      · obtain ⟨k, -, hk⟩ := mem_image.mp h
        rcases Sym2.eq_iff.mp hk with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact absurd hu (disjoint_left.mp hd.symm (g_mem _))
        · exact absurd hu (disjoint_left.mp hd.symm (g_mem _))
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hside.mp hu
        · exact hside.mpr hu
    exact not_reachable_of_closed (W1 : Set V) (Finset.mem_coe.mpr (f_mem 0))
      (fun h => disjoint_left.mp hd (Finset.mem_coe.mp h) (g_mem 0)) hclosed
      (hT.connected.preconnected (f 0) (g 0))
  -- assemble
  have key : ∀ x' y', x' ∈ W1 → y' ∈ W2 → s(x, y) = s(x', y') → Nonempty (TwoPaths T) := by
    intro x' y' hx' hy' hxy'
    obtain ⟨i, hi, rfl⟩ := W1_cover x' hx'
    obtain ⟨j, hj, rfl⟩ := W2_cover y' hy'
    refine ⟨⟨p1.length + 1, p2.length + 1, f, g, i, j, hi, hj, f_inj, g_inj,
      fun k m _ _ => fg_ne k m, fun u v => ?_⟩⟩
    rw [← SimpleGraph.mem_edgeSet, ← T.mem_edgeFinset, hedges, hxy']
    simp only [EP, EQ, mem_image, mem_range]
    constructor
    · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩ | h)
      · exact Or.inl ⟨k, by omega, h.symm⟩
      · exact Or.inr (Or.inl ⟨k, by omega, h.symm⟩)
      · exact Or.inr (Or.inr h)
    · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩ | h)
      · exact Or.inl ⟨k, by omega, h.symm⟩
      · exact Or.inr (Or.inl ⟨k, by omega, h.symm⟩)
      · exact Or.inr (Or.inr h)
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact key x y hx hy rfl
  · exact key y x hy hx Sym2.eq_swap

/-! ### The conjecture -/

/-- **WOWII Conjecture 372.** For a tree `T` on at least three vertices that is not a path,
`v_c(T) ≤ (p(T) - 1) γ_t(T)`. -/
theorem conjecture372 (T : SimpleGraph V) (hT : T.IsTree) (hn : 3 ≤ Fintype.card V)
    (hp : 2 ≤ pathCoverNumber T) :
    vertexCoverNum T ≤ (pathCoverNumber T - 1) * totalDomNum T := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnoiso : ∀ v, ∃ u, T.Adj v u := fun v =>
    (T.degree_pos_iff_exists_adj v).mp (hT.connected.preconnected.degree_pos_of_nontrivial v)
  obtain ⟨S, hS, hScard⟩ := exists_tds_card_eq hnoiso
  rcases Nat.lt_or_ge (pathCoverNumber T) 3 with h2 | h3
  · have hp2 : pathCoverNumber T = 2 := by omega
    obtain ⟨P, hPcard, hP⟩ := exists_pathCover_card_eq T
    obtain ⟨H⟩ := exists_twoPaths hT hP (hPcard.trans hp2)
    rw [hp2, ← hScard]
    simpa using H.vc_le_tds hS
  · obtain ⟨C, hC, hCcard⟩ := exists_vc_of_tds hT hS
    have := vertexCoverNum_le hC
    rw [← hScard]
    calc vertexCoverNum T ≤ 2 * #S := by omega
      _ ≤ (pathCoverNumber T - 1) * #S := Nat.mul_le_mul_right _ (by omega)

/-- **WOWII Conjecture 372**, as stated: `γ_t(T) ≥ v_c(T) / (p(T) - 1)` for every tree `T` on
more than two vertices, with the convention `x / 0 = 0` when `T` is a path. -/
theorem conjecture372_real (T : SimpleGraph V) (hT : T.IsTree) (hn : 3 ≤ Fintype.card V) :
    (vertexCoverNum T : ℝ) / ((pathCoverNumber T : ℝ) - 1) ≤ totalDomNum T := by
  rcases le_or_gt 2 (pathCoverNumber T) with hp | hp
  · have h := conjecture372 T hT hn hp
    have h2 : (2 : ℝ) ≤ pathCoverNumber T := by exact_mod_cast hp
    have hpos : (0 : ℝ) < (pathCoverNumber T : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hpos]
    have hcast : ((pathCoverNumber T - 1 : ℕ) : ℝ) = (pathCoverNumber T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    calc (vertexCoverNum T : ℝ) ≤ (((pathCoverNumber T - 1) * totalDomNum T : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = totalDomNum T * ((pathCoverNumber T : ℝ) - 1) := by
          rw [Nat.cast_mul, hcast]
          ring
  · have h1 : (pathCoverNumber T : ℝ) ≤ 1 := by exact_mod_cast (by omega : pathCoverNumber T ≤ 1)
    have hq : (vertexCoverNum T : ℝ) / ((pathCoverNumber T : ℝ) - 1) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    linarith [(Nat.cast_nonneg (totalDomNum T) : (0 : ℝ) ≤ totalDomNum T)]

end WOWII372
