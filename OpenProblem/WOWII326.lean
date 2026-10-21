import OpenProblem.WOWII372

/-!
# Written on the Wall II, Conjecture 326

E. DeLaViña's *Written on the Wall II* lists as open:

> **Conjecture 326.** Let `G` be a simple connected graph with `n > 1`. If `3 μ(G) ≤ |E(S)|`,
> where `S` is the set of vertices of degree two, then `G` is well totally dominated.

Here `μ` is the matching number, `E(S)` the set of edges joining two vertices of degree two, and
`G` is *well totally dominated* if all minimal total dominating sets have the same size.

We prove the conjecture (`conjecture326`) by showing that its hypothesis forces `G` to be a
triangle (`eq_triangle`), which is well totally dominated.

Let `M` be a maximum matching and let `F = E(S)`.

* Every edge of `F` meets an edge of `M`, otherwise `M` could be enlarged.
* An edge `uv ∈ M` meets at most three edges of `F`, with equality only if `u` and `v` have degree
  two and all edges at `u` and `v` lie in `F`.

So `3|M| ≤ |F|` forces equality for every edge of `M`. Take `uv ∈ M`, and let `x` and `y` be the
other neighbours of `u` and `v`. Neither `x` nor `y` is covered by `M`: an edge `xz ∈ M` would meet
all three edges at `x` and `z`, including `ux`, which is already counted for `uv`. If `x ≠ y`, then
`x - u - v - y` is an augmenting path, which is impossible. So `x = y`, and `u, v, x` form a
triangle of degree-two vertices, which is all of `G`.
-/

open Finset

open scoped Classical

noncomputable section

namespace WOWII326

open SimpleGraph WOWII372

variable {V : Type*} [Fintype V]

/-! ### Definitions -/

/-- `S` is a minimal total dominating set. -/
def IsMinTDS (G : SimpleGraph V) (S : Finset V) : Prop := IsTDS G S ∧ ∀ T ⊂ S, ¬ IsTDS G T

/-- `G` is well totally dominated: all minimal total dominating sets have the same size. -/
def WellTotallyDominated (G : SimpleGraph V) : Prop :=
  ∀ S T, IsMinTDS G S → IsMinTDS G T → #S = #T

/-- `M` is a matching: a set of pairwise disjoint edges. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ e, v ∉ f

/-- The matching number `μ(G)`. -/
def matchingNumber (G : SimpleGraph V) : ℕ := sSup {k | ∃ M, IsMatching G M ∧ #M = k}

/-- The edges joining two vertices of degree two. -/
def E2 (G : SimpleGraph V) : Finset (Sym2 V) := G.edgeFinset.filter fun e => ∀ v ∈ e, G.degree v = 2

/-! ### Matchings -/

lemma bddAbove_matchings (G : SimpleGraph V) : BddAbove {k | ∃ M, IsMatching G M ∧ #M = k} :=
  ⟨#G.edgeFinset, fun _ ⟨_, hM, hk⟩ => hk ▸ card_le_card hM.1⟩

lemma card_le_matchingNumber {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M) :
    #M ≤ matchingNumber G :=
  le_csSup (bddAbove_matchings G) ⟨M, hM, rfl⟩

lemma exists_max_matching (G : SimpleGraph V) :
    ∃ M, IsMatching G M ∧ #M = matchingNumber G :=
  Nat.sSup_mem (s := {k | ∃ M, IsMatching G M ∧ #M = k}) ⟨0, ∅, ⟨empty_subset _, by simp⟩, rfl⟩
    (bddAbove_matchings G)

/-! ### Edges of `E(S)` meeting a given edge -/

/-- The edges of `E(S)` that meet `s(u, v)`: at most three, and exactly three only if `u` and `v`
have degree two and every edge at `u` or `v` lies in `E(S)`. -/
lemma meet_E2 {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (h3 : 3 ≤ #((E2 G).filter fun e => ∃ w ∈ e, w ∈ s(u, v))) :
    G.degree u = 2 ∧ G.degree v = 2 ∧
      (E2 G).filter (fun e => ∃ w ∈ e, w ∈ s(u, v)) = G.incidenceFinset u ∪ G.incidenceFinset v := by
  set A := (E2 G).filter fun e => ∃ w ∈ e, w ∈ s(u, v)
  have hAsub : ∀ w, ∀ e ∈ A, w ∈ e → w ∈ s(u, v) → G.degree w = 2 ∧ e ∈ G.incidenceFinset w := by
    intro w e he hwe _
    have he2 := (mem_filter.mp (mem_filter.mp he).1)
    exact ⟨he2.2 w hwe, mem_incidenceFinset.mpr ⟨G.mem_edgeFinset.mp he2.1, hwe⟩⟩
  have hsplit : A ⊆ (A.filter fun e => u ∈ e) ∪ (A.filter fun e => v ∈ e) := by
    intro e he
    obtain ⟨w, hwe, hw⟩ := (mem_filter.mp he).2
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact mem_union_left _ (mem_filter.mpr ⟨he, hwe⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨he, hwe⟩)
  have hu_sub : A.filter (fun e => u ∈ e) ⊆ G.incidenceFinset u := fun e he =>
    (hAsub u e (mem_filter.mp he).1 (mem_filter.mp he).2 (Sym2.mem_mk_left u v)).2
  have hv_sub : A.filter (fun e => v ∈ e) ⊆ G.incidenceFinset v := fun e he =>
    (hAsub v e (mem_filter.mp he).1 (mem_filter.mp he).2 (Sym2.mem_mk_right u v)).2
  have hcu := card_incidenceFinset_eq_degree G u
  have hcv := card_incidenceFinset_eq_degree G v
  -- if no edge of `A` contains `u`, then `|A| ≤ 2`
  have hdu : G.degree u = 2 := by
    by_contra hne
    have hempty : A.filter (fun e => u ∈ e) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hue
      exact hne (hAsub u e he hue (Sym2.mem_mk_left u v)).1
    have hle : #A ≤ #(A.filter fun e => v ∈ e) := by
      calc #A ≤ #((A.filter fun e => u ∈ e) ∪ (A.filter fun e => v ∈ e)) := card_le_card hsplit
        _ = _ := by rw [hempty, empty_union]
    have hv2 : #(A.filter fun e => v ∈ e) ≤ 2 := by
      by_cases hv : (A.filter fun e => v ∈ e).Nonempty
      · obtain ⟨e, he⟩ := hv
        have := (hAsub v e (mem_filter.mp he).1 (mem_filter.mp he).2 (Sym2.mem_mk_right u v)).1
        have := card_le_card hv_sub
        omega
      · rw [not_nonempty_iff_eq_empty.mp hv]; simp
    omega
  have hdv : G.degree v = 2 := by
    by_contra hne
    have hempty : A.filter (fun e => v ∈ e) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hve
      exact hne (hAsub v e he hve (Sym2.mem_mk_right u v)).1
    have hle : #A ≤ #(A.filter fun e => u ∈ e) := by
      calc #A ≤ #((A.filter fun e => u ∈ e) ∪ (A.filter fun e => v ∈ e)) := card_le_card hsplit
        _ = _ := by rw [hempty, union_empty]
    have := card_le_card hu_sub
    omega
  refine ⟨hdu, hdv, ?_⟩
  -- `A ⊆ I_u ∪ I_v`, which has exactly three elements
  have hsubI : A ⊆ G.incidenceFinset u ∪ G.incidenceFinset v :=
    hsplit.trans (union_subset_union hu_sub hv_sub)
  have hinter : G.incidenceFinset u ∩ G.incidenceFinset v = {s(u, v)} := by
    ext e
    simp only [mem_inter, mem_incidenceFinset, mem_singleton]
    constructor
    · rintro ⟨⟨_, hu⟩, ⟨_, hv⟩⟩
      exact (Sym2.mem_and_mem_iff (G.ne_of_adj huv)).mp ⟨hu, hv⟩
    · rintro rfl
      exact ⟨⟨huv, Sym2.mem_mk_left u v⟩, ⟨huv, Sym2.mem_mk_right u v⟩⟩
  have hcard : #(G.incidenceFinset u ∪ G.incidenceFinset v) = 3 := by
    have := card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    rw [hinter, card_singleton] at this
    omega
  exact eq_of_subset_of_card_le hsubI (by omega)

/-! ### The hypothesis forces a triangle -/

/-- If `3 μ(G) ≤ |E(S)|` for a connected graph on at least two vertices, then `G` is a triangle. -/
lemma eq_triangle {G : SimpleGraph V} (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (h : 3 * matchingNumber G ≤ #(E2 G)) :
    ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧ ∀ w, w = a ∨ w = b ∨ w = c := by
  obtain ⟨M, hM, hMcard⟩ := exists_max_matching G
  have hmax : ∀ M', IsMatching G M' → #M' ≤ #M := fun M' hM' =>
    hMcard ▸ card_le_matchingNumber hM'
  -- every edge of `E(S)` meets `M`
  have hcover : ∀ e ∈ E2 G, ∃ m ∈ M, ∃ w ∈ e, w ∈ m := by
    intro e he
    by_contra hno
    push Not at hno
    have heE : e ∈ G.edgeFinset := (mem_filter.mp he).1
    have heM : e ∉ M := by
      intro heM
      exact hno e heM e.out.1 (Sym2.out_fst_mem e) (Sym2.out_fst_mem e)
    have hM' : IsMatching G (insert e M) := by
      refine ⟨insert_subset heE hM.1, ?_⟩
      intro f hf g hg hfg w hwf hwg
      rcases mem_insert.mp hf with hf' | hf' <;> rcases mem_insert.mp hg with hg' | hg'
      · exact hfg (hf'.trans hg'.symm)
      · subst hf'; exact hno g hg' w hwf hwg
      · subst hg'; exact hno f hf' w hwg hwf
      · exact hM.2 f hf' g hg' hfg w hwf hwg
    have := hmax _ hM'
    rw [card_insert_of_notMem heM] at this
    omega
  choose! c hcM hc using hcover
  set fib := fun m => (E2 G).filter fun e => c e = m
  have hsum : #(E2 G) = ∑ m ∈ M, #(fib m) := card_eq_sum_card_fiberwise hcM
  -- a fiber consists of edges of `E(S)` meeting its edge
  have hfib_sub : ∀ m ∈ M, ∀ u v, m = s(u, v) →
      fib m ⊆ (E2 G).filter fun e => ∃ w ∈ e, w ∈ s(u, v) := by
    intro m _ u v hm e he
    rw [mem_filter] at he ⊢
    obtain ⟨w, hwe, hwm⟩ := hc e he.1
    refine ⟨he.1, w, hwe, ?_⟩
    rw [← hm, ← he.2]
    exact hwm
  have hadjM : ∀ m ∈ M, ∃ u v, G.Adj u v ∧ m = s(u, v) := by
    intro m hm
    have hmE := hM.1 hm
    induction m using Sym2.ind with
    | h u v => exact ⟨u, v, G.mem_edgeFinset.mp hmE, rfl⟩
  have hfib3 : ∀ m ∈ M, #(fib m) ≤ 3 := by
    intro m hm
    obtain ⟨u, v, huv, rfl⟩ := hadjM m hm
    by_contra hlt
    have h3 : 3 ≤ #((E2 G).filter fun e => ∃ w ∈ e, w ∈ s(u, v)) :=
      (by omega : 3 ≤ #(fib s(u, v))).trans (card_le_card (hfib_sub _ hm u v rfl))
    obtain ⟨-, -, hA⟩ := meet_E2 huv h3
    have := card_le_card (hfib_sub _ hm u v rfl)
    rw [hA] at this
    have h4 := card_union_le (G.incidenceFinset u) (G.incidenceFinset v)
    have hinter : s(u, v) ∈ G.incidenceFinset u ∩ G.incidenceFinset v := by
      simp only [mem_inter, mem_incidenceFinset]
      exact ⟨⟨huv, Sym2.mem_mk_left u v⟩, ⟨huv, Sym2.mem_mk_right u v⟩⟩
    have h5 := card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    have h6 := card_pos.mpr ⟨_, hinter⟩
    have h7 : G.degree u = 2 ∧ G.degree v = 2 := ⟨(meet_E2 huv h3).1, (meet_E2 huv h3).2.1⟩
    rw [card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree, h7.1, h7.2] at h5
    omega
  -- `M` is nonempty, since `G` has an edge
  obtain ⟨a0, b0, hab0⟩ : ∃ a b : V, G.Adj a b := by
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a⟩ := hG.nonempty
    obtain ⟨b, hb⟩ := (G.degree_pos_iff_exists_adj a).mp (hG.preconnected.degree_pos_of_nontrivial a)
    exact ⟨a, b, hb⟩
  have hMpos : 0 < #M := by
    have : IsMatching G {s(a0, b0)} := ⟨by simpa using hab0, by simp⟩
    have h1 := hmax _ this
    rw [card_singleton] at h1
    omega
  -- every fiber has exactly three edges
  have hfib_eq : ∀ m ∈ M, #(fib m) = 3 := by
    by_contra hne
    push Not at hne
    obtain ⟨m, hm, hm3⟩ := hne
    have hlt : ∑ m ∈ M, #(fib m) < ∑ _m ∈ M, 3 :=
      Finset.sum_lt_sum (fun m hm => hfib3 m hm) ⟨m, hm, by have := hfib3 m hm; omega⟩
    rw [sum_const, smul_eq_mul] at hlt
    rw [← hMcard] at h
    omega
  -- structure around an edge of `M`
  have hstruct : ∀ m ∈ M, ∀ u v, G.Adj u v → m = s(u, v) →
      G.degree u = 2 ∧ G.degree v = 2 ∧ fib m = G.incidenceFinset u ∪ G.incidenceFinset v := by
    intro m hm u v huv hmuv
    have hsub := hfib_sub m hm u v hmuv
    have h3 : 3 ≤ #((E2 G).filter fun e => ∃ w ∈ e, w ∈ s(u, v)) :=
      (hfib_eq m hm).symm.le.trans (card_le_card hsub)
    obtain ⟨hdu, hdv, hA⟩ := meet_E2 huv h3
    refine ⟨hdu, hdv, ?_⟩
    rw [hA] at hsub
    apply eq_of_subset_of_card_le hsub
    rw [hfib_eq m hm]
    have := card_union_le (G.incidenceFinset u) (G.incidenceFinset v)
    rw [card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree, hdu, hdv] at this
    have h3' := card_le_card hsub
    rw [hfib_eq m hm] at h3'
    have h5 := card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    rw [card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree, hdu, hdv] at h5
    have hinter : s(u, v) ∈ G.incidenceFinset u ∩ G.incidenceFinset v := by
      simp only [mem_inter, mem_incidenceFinset]
      exact ⟨⟨huv, Sym2.mem_mk_left u v⟩, ⟨huv, Sym2.mem_mk_right u v⟩⟩
    have h6 := card_pos.mpr ⟨_, hinter⟩
    omega
  -- pick an edge `uv ∈ M`
  obtain ⟨m, hm⟩ := card_pos.mp hMpos
  obtain ⟨u, v, huv, rfl⟩ := hadjM m hm
  obtain ⟨hdu, hdv, hfibuv⟩ := hstruct _ hm u v huv rfl
  -- the other neighbours `x` of `u` and `y` of `v`
  obtain ⟨x, hux, hxv⟩ : ∃ x, G.Adj u x ∧ x ≠ v := by
    obtain ⟨x, hx, hne⟩ := Finset.exists_mem_ne
      (by rw [card_neighborFinset_eq_degree]; omega : 1 < #(G.neighborFinset u)) v
    exact ⟨x, (G.mem_neighborFinset u x).mp hx, hne⟩
  obtain ⟨y, hvy, hyu⟩ : ∃ y, G.Adj v y ∧ y ≠ u := by
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne
      (by rw [card_neighborFinset_eq_degree]; omega : 1 < #(G.neighborFinset v)) u
    exact ⟨y, (G.mem_neighborFinset v y).mp hy, hne⟩
  have hux_fib : s(u, x) ∈ fib s(u, v) := by
    rw [hfibuv]
    exact mem_union_left _ (mem_incidenceFinset.mpr ⟨hux, Sym2.mem_mk_left u x⟩)
  have hvy_fib : s(v, y) ∈ fib s(u, v) := by
    rw [hfibuv]
    exact mem_union_right _ (mem_incidenceFinset.mpr ⟨hvy, Sym2.mem_mk_left v y⟩)
  -- `x` and `y` are not covered by `M`
  have hunc : ∀ z w, G.Adj z w → s(z, w) ∈ fib s(u, v) → z ≠ u → z ≠ v → ∀ m' ∈ M, z ∉ m' := by
    intro z w hzw hfz hzu hzv m' hm' hzm'
    have hzE2 : s(z, w) ∈ E2 G := (mem_filter.mp hfz).1
    have hcz : c s(z, w) = s(u, v) := (mem_filter.mp hfz).2
    obtain ⟨a, b, hab, rfl⟩ := hadjM m' hm'
    have hne : s(a, b) ≠ s(u, v) := by
      intro heq
      rw [heq] at hzm'
      rcases Sym2.mem_iff.mp hzm' with h | h
      · exact hzu h
      · exact hzv h
    obtain ⟨-, -, hfab⟩ := hstruct _ hm' a b hab rfl
    have hmem : s(z, w) ∈ fib s(a, b) := by
      rw [hfab]
      rcases Sym2.mem_iff.mp hzm' with rfl | rfl
      · exact mem_union_left _ (mem_incidenceFinset.mpr ⟨hzw, Sym2.mem_mk_left _ _⟩)
      · exact mem_union_right _ (mem_incidenceFinset.mpr ⟨hzw, Sym2.mem_mk_left _ _⟩)
    exact hne ((mem_filter.mp hmem).2.symm.trans hcz)
  have hxu_eq : s(x, u) = s(u, x) := Sym2.eq_swap
  have hyv_eq : s(y, v) = s(v, y) := Sym2.eq_swap
  have hxunc := hunc x u hux.symm (hxu_eq ▸ hux_fib) (G.ne_of_adj hux).symm hxv
  have hyunc := hunc y v hvy.symm (hyv_eq ▸ hvy_fib) hyu (G.ne_of_adj hvy).symm
  by_cases hxy : x = y
  · -- a triangle of degree-two vertices
    subst hxy
    refine ⟨u, v, x, huv, hvy, hux, ?_⟩
    have hnu : ∀ w, G.Adj u w → w = v ∨ w = x := by
      intro w hw
      have hN : G.neighborFinset u = {v, x} := by
        apply (eq_of_subset_of_card_le _ _).symm
        · intro z hz
          rcases mem_insert.mp hz with rfl | hz
          · exact (G.mem_neighborFinset u z).mpr huv
          · rw [mem_singleton.mp hz]; exact (G.mem_neighborFinset u x).mpr hux
        · rw [card_neighborFinset_eq_degree, hdu, card_pair hxv.symm]
      have : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hw
      rw [hN] at this
      simpa using this
    have hnv : ∀ w, G.Adj v w → w = u ∨ w = x := by
      intro w hw
      have hN : G.neighborFinset v = {u, x} := by
        apply (eq_of_subset_of_card_le _ _).symm
        · intro z hz
          rcases mem_insert.mp hz with rfl | hz
          · exact (G.mem_neighborFinset v z).mpr huv.symm
          · rw [mem_singleton.mp hz]; exact (G.mem_neighborFinset v x).mpr hvy
        · rw [card_neighborFinset_eq_degree, hdv, card_pair hyu.symm]
      have : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).mpr hw
      rw [hN] at this
      simpa using this
    have hdx : G.degree x = 2 := (mem_filter.mp (mem_filter.mp hux_fib).1).2 x (Sym2.mem_mk_right u x)
    have hnx : ∀ w, G.Adj x w → w = u ∨ w = v := by
      intro w hw
      have hN : G.neighborFinset x = {u, v} := by
        apply (eq_of_subset_of_card_le _ _).symm
        · intro z hz
          rcases mem_insert.mp hz with rfl | hz
          · exact (G.mem_neighborFinset x z).mpr hux.symm
          · rw [mem_singleton.mp hz]; exact (G.mem_neighborFinset x v).mpr hvy.symm
        · rw [card_neighborFinset_eq_degree, hdx, card_pair (G.ne_of_adj huv)]
      have : w ∈ G.neighborFinset x := (G.mem_neighborFinset x w).mpr hw
      rw [hN] at this
      simpa using this
    have hcl : ∀ a b, G.Adj a b → a ∈ ({u, v, x} : Set V) → b ∈ ({u, v, x} : Set V) := by
      intro a b hab ha
      rcases ha with rfl | rfl | rfl
      · rcases hnu b hab with rfl | rfl <;> simp
      · rcases hnv b hab with rfl | rfl <;> simp
      · rcases hnx b hab with rfl | rfl <;> simp
    intro w
    by_contra hw
    push Not at hw
    exact not_reachable_of_closed ({u, v, x} : Set V) (by simp) (by simp [hw.1, hw.2.1, hw.2.2])
      hcl (hG.preconnected u w)
  · -- an augmenting path `x - u - v - y`
    exfalso
    let M' := insert s(u, x) (insert s(v, y) (M.erase s(u, v)))
    have hvyM : s(v, y) ∉ M.erase s(u, v) := fun h =>
      hyunc _ (mem_of_mem_erase h) (Sym2.mem_mk_right v y)
    have huxM : s(u, x) ∉ insert s(v, y) (M.erase s(u, v)) := by
      intro h
      rcases mem_insert.mp h with h | h
      · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact G.ne_of_adj huv h1
        · exact hyu.symm h1
      · exact hxunc _ (mem_of_mem_erase h) (Sym2.mem_mk_right u x)
    have huvnot : ∀ f ∈ M.erase s(u, v), u ∉ f ∧ v ∉ f := by
      intro f hf
      have hfM := mem_of_mem_erase hf
      have hfne := ne_of_mem_erase hf
      exact ⟨fun h => hM.2 _ hm f hfM hfne.symm u (Sym2.mem_mk_left u v) h,
        fun h => hM.2 _ hm f hfM hfne.symm v (Sym2.mem_mk_right u v) h⟩
    have hM' : IsMatching G M' := by
      refine ⟨?_, ?_⟩
      · refine insert_subset (G.mem_edgeFinset.mpr hux) (insert_subset (G.mem_edgeFinset.mpr hvy) ?_)
        exact (erase_subset _ _).trans hM.1
      · -- the vertices of the two new edges are free in `M.erase s(u, v)`
        have hfree : ∀ f ∈ M.erase s(u, v), ∀ w, w ∈ s(u, x) ∨ w ∈ s(v, y) → w ∉ f := by
          intro f hf w hw hwf
          rcases hw with hw | hw <;> rcases Sym2.mem_iff.mp hw with rfl | rfl
          · exact (huvnot f hf).1 hwf
          · exact hxunc f (mem_of_mem_erase hf) hwf
          · exact (huvnot f hf).2 hwf
          · exact hyunc f (mem_of_mem_erase hf) hwf
        have hdisj : ∀ w, w ∈ s(u, x) → w ∉ s(v, y) := by
          intro w hw1 hw2
          rcases Sym2.mem_iff.mp hw1 with rfl | rfl <;> rcases Sym2.mem_iff.mp hw2 with h | h
          · exact G.ne_of_adj huv h
          · exact hyu h.symm
          · exact hxv h
          · exact hxy h
        intro e he f hf hef w hwe hwf
        rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
        · exact hef rfl
        · rcases mem_insert.mp hf with rfl | hf
          · exact hdisj w hwe hwf
          · exact hfree f hf w (Or.inl hwe) hwf
        · rcases mem_insert.mp he with rfl | he
          · exact hdisj w hwf hwe
          · exact hfree e he w (Or.inl hwf) hwe
        · rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
          · exact hef rfl
          · exact hfree f hf w (Or.inr hwe) hwf
          · exact hfree e he w (Or.inr hwf) hwe
          · exact hM.2 e (mem_of_mem_erase he) f (mem_of_mem_erase hf) hef w hwe hwf
    have := hmax _ hM'
    rw [card_insert_of_notMem huxM, card_insert_of_notMem hvyM, card_erase_of_mem hm] at this
    omega

/-! ### The triangle is well totally dominated -/

omit [Fintype V] in
lemma triangle_wtd {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : G.Adj a c) (hall : ∀ w, w = a ∨ w = b ∨ w = c) : WellTotallyDominated G := by
  have key : ∀ S, IsMinTDS G S → #S = 2 := by
    intro S ⟨hS, hmin⟩
    have hle : #S ≤ #({a, b, c} : Finset V) := card_le_card fun w _ => by
      rcases hall w with rfl | rfl | rfl <;> simp
    have h3 := card_le_three (a := a) (b := b) (c := c)
    -- at least two vertices: a vertex is not its own neighbour
    have hge : 2 ≤ #S := by
      by_contra hlt
      obtain ⟨u, hu, hau⟩ := hS a
      have hS1 : #S ≤ 1 := by omega
      obtain ⟨w, hw, hwu⟩ := hS u
      exact G.ne_of_adj hwu (card_le_one.mp hS1 _ hu _ hw)
    -- not all three: dropping `a` leaves a total dominating set
    have hne3 : #S ≠ 3 := by
      intro h3'
      have hSabc : S = {a, b, c} := by
        apply eq_of_subset_of_card_le
        · intro w hw; rcases hall w with rfl | rfl | rfl <;> simp
        · omega
      have hT : IsTDS G {b, c} := by
        intro w
        rcases hall w with rfl | rfl | rfl
        · exact ⟨b, by simp, hab⟩
        · exact ⟨c, by simp, hbc⟩
        · exact ⟨b, by simp, hbc.symm⟩
      refine hmin {b, c} ?_ hT
      rw [hSabc]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun w hw => by
        simp only [mem_insert, mem_singleton] at hw ⊢; tauto, ?_⟩
      intro heq
      have : a ∈ ({b, c} : Finset V) := heq ▸ (by simp : a ∈ ({a, b, c} : Finset V))
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · exact G.ne_of_adj hab h
      · exact G.ne_of_adj hac h
    omega
  intro S T hS hT
  rw [key S hS, key T hT]

/-- **WOWII Conjecture 326.** If `G` is connected with at least two vertices and
`3 μ(G) ≤ |E(S)|`, where `S` is the set of vertices of degree two, then `G` is well totally
dominated. -/
theorem conjecture326 (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (h : 3 * matchingNumber G ≤ #(E2 G)) : WellTotallyDominated G := by
  obtain ⟨a, b, c, hab, hbc, hac, hall⟩ := eq_triangle hG hn h
  exact triangle_wtd hab hbc hac hall

end WOWII326
