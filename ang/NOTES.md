# Ang's conjecture (OEIS A060957): research notes

**Status: the conjecture is NOT solved here.** This file records reductions, one fully
proved special case, counterexamples to natural generalisations, and computational
evidence. Everything marked *Proved* has a complete pen-and-paper proof below; everything
marked *Verified* is computational evidence only.

## The conjecture

Let `P(n)` be the set of products of subsets of `{1,…,n}`. For a prime `p ≤ n`, if
`m ∈ P(n)` and `p^a·m ∈ P(n)`, then `p^k·m ∈ P(n)` for every `0 < k < a`
(Yan Sheng Ang, 2020; `OeisA60957.conjecture` in google-deepmind/formal-conjectures,
tagged `research open`).

## Reformulation

Write each `x ≤ n` as `x = p^t·r` with `p ∤ r`. A subset `S` has product
`p^{Σt}·∏r`. Fix the `p`-free part `R`. The conjecture says that
`W(R) = { Σ_{x∈S} t(x) : S ⊆ [n], ∏ r(x) = R }` is an interval of integers.

In exponent coordinates (one coordinate per prime `q ≠ p`) the `p`-free numbers
`r ≤ n` form a down-set `D ⊂ ℕ^d`, and the elements of `[n]` form *columns*
`{(r,0),(r,1),…,(r,J_r)}` with `J_r = ⌊log_p(n/r)⌋`. The column over `r = 1`
(the powers of `p`) adds the interval `[0, T]`, `T = J_1(J_1+1)/2`, to every
fibre, so `W(R) = V(R) + [0,T]`. Here `V(R)` uses only the columns with `r ≥ 2`.

For a system of columns let `B(u)` be the set of height-sums of subsets whose
base-sum is `u`. Then `B(u) = ⋃_c [L(c), H(c)]` over count vectors `c`, with
`L(c) = Σ C(c_r,2)` and `H(c) = Σ (c_r J_r − C(c_r,2))`.

## Proved results

### 1. Two-dimensional skylines (the case of two primes)

**Theorem.** Let `K ≥ 0` and let `h_0,…,h_K ≥ 1` be arbitrary column heights.
Let `I = {(a,t) : 0 ≤ a ≤ K, 0 ≤ t < h_a}`. For every `A`, the set
`T_A = { Σ_{(a,t)∈S} t : S ⊆ I, Σ_{(a,t)∈S} a = A }` is an interval.

*Corollary.* For primes `p ≠ q` and any `n`, the products of subsets of the
`{p,q}`-smooth numbers `≤ n` satisfy Ang's property for `p` (and for `q`).

**Formalised in Lean 4 / Mathlib** (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound` only):

* `Skyline.reach_interval` (`OpenProblem/Skyline.lean`): the skyline theorem.
* `TwoPrimes.ang_two_primes` (`OpenProblem/TwoPrimes.lean`): if `m` and `p^e·m` are
  products of subsets of `TwoPrimes.smooth p q n = {x ≤ n : x = q^a·p^t}`, then so is
  `p^k·m` for every `k ≤ e`.

*Proof.* Induction on `Σ h_a`, raising one column at a time from the base
`h ≡ 1`. Invariant `INV(h)`:

* (G) every `T_A` is an interval;
* (KL) for every column `a` and every `A` with `T_A ≠ ∅ ≠ T_{A−a}`,
  `T_A ∩ (h_a − 1 + T_{A−a}) ≠ ∅`.

The reachable set `R = {A : T_A ≠ ∅}` equals `[0, Σ a·h_a]`, because the
multiset contains each of `1,…,K`. Base: every `T_A` is `{0}` or empty.

Step: raise column `a₀` by adding `(a₀, h_{a₀})`. Then
`T⁺_A = T_A ∪ (h_{a₀} + T_{A−a₀})`.

* (G⁺): KL at `(A, a₀)` gives `x ∈ T_A` with `x+1 ∈ h_{a₀} + T_{A−a₀}`, so the
  union is an interval.
* (KL⁺) for `a = a₀`: if `T_{A−a₀} ≠ ∅`, then `h_{a₀} + T_{A−a₀}` lies in both
  sets. Otherwise `A` and `A − 2a₀` are in `R` while `A − a₀` is not, which is
  impossible since `R` is an interval.
* (KL⁺) for `a ≠ a₀`: if `A, A−a ∈ R`, use KL at `(A,a)`. If
  `A−a₀, A−a−a₀ ∈ R`, use KL at `(A−a₀, a)` shifted by `h_{a₀}`. In the
  remaining cases, either `A, A−a−a₀ ∈ R` and `A−a ∉ R` (impossible, `R` is an
  interval), or `A ∉ R`, `A−a₀ ∈ R`, `A−a ∈ R`, `A−a−a₀ ∉ R`. The last forces
  `max R < A < a + a₀ ≤ max R`, a contradiction, because `max R ≥ Σ_{b=1}^K b ≥ a + a₀`.

The column over `0` is covered by the same argument. Its KL condition says
`T_A` has length at least `h_0 − 1`. ∎

### 2. The general propagation lemma (any dimension)

Fix a down-set `D ⊂ ℕ^d` and column heights `J` on `D∖{0}`. Let `R` be the set
of reachable base-sums and `m = J+1`. Suppose that before raising column `w₀`
the reachable set satisfies

* **R1**: `u, u−2w₀ ∈ R ⇒ u−w₀ ∈ R`;
* **R2**: `x+w₀, x+v ∈ R ⇒ x ∈ R or x+w₀+v ∈ R` (any `x ∈ ℤ^d`);
* **R3**: `x, x+w₀+v ∈ R ⇒ x+w₀ ∈ R or x+v ∈ R`;

for all columns `v ≠ w₀`. Then (G)+(KL) for all columns is preserved by the
raise. The proof is the case analysis of §1, where the three impossible
configurations are excluded by R1–R3 instead of by "`R` is an interval".

### 3. Hole-freeness implies R1–R3

Let `Z = Σ_w [0, m_w·w]`. If `R = Z ∩ ℤ^d` ("hole-free"), then R1–R3 hold.
R1 is convexity. R2 and R3 follow by writing `Z = K + [0,w] + [0,v]` and taking
a convex combination of two representations (the λ-interval argument).

Raising multiplicities preserves hole-freeness. If `R = Z ∩ ℤ^d` and `m_w ≥ 1`,
then `R + {0,w}` equals `(Z + [0,w]) ∩ ℤ^d`.

### Consequence (conditional), and why it cannot finish the proof

If the set of products of *distinct* `p`-free integers in `[2,N]` were hole-free
in exponent space (**HF_int(N,p)**), §2–§3 would give interval fibres `V(R)`
for every column system over the `p`-free numbers `≤ N`. That would hold even
without the powers of `p`.

**This fails for large `N`.** HF_int(N,p) holds for `N ≤ 60` (`p = 2`) and
`N ≤ 50` (`p = 3`). But the `{3,5,7}`-smooth slice already has holes at
`N = 2000` (`experiments/smooth3.cpp`). That slice embeds exactly into the full
system: a product with `{3,5,7}`-smooth `p`-free part can only use smooth
elements. Moreover:

* **The powers of `p` are genuinely needed.** For `n = 2000`, `p = 2` there is
  an odd `R` (`{3,5,7}`-smooth) for which `V(R)`, the set of 2-adic valuations
  of products of subsets of `[2000] ∖ {1,2,4,…,1024}` with odd part `R`, has a
  gap of size 3 (`experiments/smoothang16.cpp`). The powers of 2 provide slack
  `T = 55`, so Ang's property itself still holds there. In the same slice,
  `n = 1000` and `n = 5000` have no gaps at all.
* Degenerate reachability configurations (failures of R1) do occur at raise
  steps in that slice at `N = 2000` (`experiments/smoothff.cpp`).

So any proof of the full conjecture must use the slack `T` from the powers of
`p` in an essential way.

### 4. A reduction that does use the slack `T`

A *quadratic move* replaces at most two factors of a factorization `c` of `R`
by at most two factors with the same product (within the capacities
`c_r ≤ J_r + 1`). Such a move changes `L(c)` by at most `2·J₁`, where
`J₁ = ⌊log_p n⌋`. Since `(J₁−1)(J₁−2) ≥ 0`, we have `2·J₁ ≤ T + 1`. Hence the
intervals `[L, H+T]` of two configurations related by a quadratic move overlap
or touch.

**Consequence.** If, for every `R`, each component of the factorizations of `R`
under quadratic moves meets every other component's interval range, then Ang's
conjecture holds. Two sufficient conditions are that quadratic moves connect all
factorizations, or that every component contains an `L`-minimiser.
For `p > √n` (`J₁ = 1`, `T = 1`) the relevant quantity is just the number `d`
of `r ≤ n/p` used twice. Quadratic moves change `d` by at most 2, and `V(R)` is
an interval as soon as `{d(c)}` has gaps of at most 2.

## Counterexamples to generalisations (all verified exactly)

* **Arbitrary heights, `d = 3`.** A down-set `D ⊂ ℕ³` with 23 columns gives a
  gap after raising column `(1,1,1)` to height 2 (`experiments/r1mono.py`). The
  fibre at `u = (6,18,8)` becomes `{…}` with a gap. So the column theorem needs
  monotone heights in general.
* **Convex down-sets with arbitrary heights.** For `5Δ₃ = {x+y+z ≤ 5}`, R1
  fails, which yields a gap after raising one column to height 2. Subset sums of
  `5Δ₃∖{0}` and of `6Δ₃∖{0}` have 12 holes each (`experiments/simplex6.cpp`).
  This mirrors Lemmens, *Convexity of distinct sum sets* (arXiv:1812.09527).
* **R2 and KL(intersect) can fail** for non-monotone multiplicities
  (`experiments/verify_r2.py`, `kl_r2.py`).
* **Columns over a difference of two down-sets** can fail (`d = 1`: columns
  `{2,3}`).

## Computational evidence

* The conjecture holds for all `n ≤ 40` and all `p` (exhaustive,
  `experiments/a60957.cpp`). It also holds for random `R` with
  `n = 50, 70, 90, 120` (`experiments/angrand.py`).
* **Stronger, without powers of `p`:** for `n ≤ 40` and `p ≤ 7`, `V(R)` itself
  is an interval (`experiments/vgap.cpp`).
* **Down-set theorem:** for random finite down-sets `I ⊂ ℕ^k` (`k ≤ 6`, up to
  90 points), subset sums are convex along every axis
  (`experiments/dsc.cpp`, `dsbig.cpp`). Every 2-D axis slice is a convex
  polyomino (`experiments/polyo.cpp`).
* **Flat-first order for integers:** start with all `p`-free `r ≤ N` at height
  0, then add `p^j r` (`j ≥ 1`) in increasing order. KL holds at every stage and
  no configuration violating R1–R3 occurs at any raise. Checked for `N ≤ 34`,
  `p ∈ {2,3,5}`, and `N ≤ 30`, `p = 7` (`experiments/flatfirst.cpp`). This
  verifies the reduction's hypothesis in that range.
* HF_int(N,p) holds (adjacent-candidate exact facet test) for `N ≤ 60`
  (`p = 2`), `N ≤ 50` (`p = 3`), `N ≤ 40` (`p = 5`) (`experiments/inthf.cpp`).
  It fails from `N = 2000` (`p = 2`) via the `{3,5,7}`-smooth slice.
* Smooth slices make large `n` testable: Ang's property holds on the
  `{3,5,7}`-smooth slice for `p = 2`, `n ∈ {1000, 2000, 5000}`, and on
  `{2,3,5,7}`-smooth slices for `p ∈ {31, 53, 97}` and `n` up to `5p`
  (`experiments/smoothang16.cpp`).
