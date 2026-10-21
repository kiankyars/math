# Graffiti-type graph conjectures: notes

Status, all verified in Lean:

- **Proved:** WOWII 178, 241, 326, 348, 372, 377 and 380.
- **Refuted:** WOWII 358, 359 and 378.
- **Resolved both ways:** WOWII 367, which is true when degree 2 is a strict mode and false when
  ties are allowed.

The files are `OpenProblem/WOWII178.lean`, `WOWII326.lean`, `WOWII241`/`WOWII380` (both in
`OpenProblem/WOWII380.lean`), `WOWII348.lean`, `WOWII358.lean` (358 and 359), `WOWII367.lean`, `WOWII372.lean`,
`WOWII377.lean` and `WOWII378.lean`.

The other conjectures below are still open. For them we record evidence and partial results only.

Source of statuses: E. DeLaViña, *Written on the Wall II* (WOWII), through the JSON
transcription of the archived "open" page, cross-checked in October 2026 against the issue
tracker of google-deepmind/formal-conjectures. Some WOWII conjectures have recently been
resolved there by other contributors, so we only claim numbers with no activity on that tracker.

## WOWII 178: proved

> If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ max_v λ(v) + max {|N(e)| : e ∈ E(G)}`.

The invariants:

- `L_s` is the maximum number of leaves of a spanning tree.
- `b` is the order of a largest induced bipartite subgraph.
- `λ(v) = α(G[N(v)])`.
- `N(uv) = N(u) ∪ N(v)`.

WOWII lists this conjecture as open, with the remark that `L_s ≥ |N(e)| - 2` and
`b ≥ λ(v) + 1` give the bound up to one.

**Proof.** Let `v` maximise `λ`, and let `I ⊆ N(v)` be independent with `|I| = λ(v)`.

- If some `w ≠ v` is not adjacent to `v`, then `G[{v, w} ∪ I]` is bipartite with parts
  `{v, w}` and `I`. So `b ≥ λ(v) + 2`, and adding `L_s ≥ |N(e)| - 2` gives the claim.
- If `v` is adjacent to all other vertices, then the star at `v` is a spanning tree, so
  `L_s = n - 1`. Since `b ≥ λ(v) + 1` and `|N(e)| ≤ n`, the claim follows.

The bound `L_s ≥ |N(e)| - 2` for `e = uv`: the double star on `e` is acyclic, so it extends to a
spanning tree `T`. In any tree, the degree sum `∑ deg = 2n - 2` gives
`deg u + deg v ≤ #leaves + 2`, and here `deg_T u + deg_T v ≥ |N(u) ∪ N(v)|`.

**Formalization.** `WOWII178.conjecture178` in `OpenProblem/WOWII178.lean` uses Mathlib only. It
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. Its definitions of
`L_s` (spanning trees), `b` and `λ` mirror those in formal-conjectures
(`SimpleGraph.Ls`, `largestInducedBipartiteSubgraphSize`, `indepNeighborsCard`).

## WOWII 348: proved

> If `T` is a tree on `n > 2` vertices, then `γ_t(T) ≥ (2/3) |N(D_2(T)) - D_2(T)|`, where
> `D_2 = {v | deg(v) = 2}`.

Here `X = N(D_2) - D_2` is the set of vertices whose degree is not 2 but which have a neighbour of
degree 2. WOWII lists this conjecture as open (dated February 2009). Its neighbours 347, 349 and 350
were proved by Hongxing Jiang in 2012.

We prove the stronger bound `3 γ_t(T) ≥ 2|X| + 2`. It is sharp, for example for a star with one
subdivided edge. The proof starts from a total dominating set `S`.

- **Edge count.** At most `|S|/2 - 1` edges avoid `S`. This is the same count as in the WOWII 372
  proof.
- **Injection.** `X` injects into `S` plus the edges avoiding `S`:
  - `x ∈ S` maps to itself;
  - otherwise, if `x` has a degree-2 neighbour `d ∉ S`, it maps to the edge `xd`;
  - otherwise, `x` maps to a degree-2 neighbour, which lies in `S`.

  Two vertices outside `S` cannot share a degree-2 neighbour `d`, since `d` would then have no
  neighbour in `S`. Vertices of `X` do not have degree 2, so the three kinds of image cannot
  collide.

Together these give `|X| ≤ |S| + |S|/2 - 1`. The computed minimum of `3 γ_t - 2|X|` over all trees
with 3 to 20 vertices is exactly 2 (`experiments/t348.cpp`). The largest ratio `|X| / γ_t` found up
to 19 vertices is `7/6`.

The cruder route through `γ_t ≥ (2/3)(v_c + 1)` fails, because `|X| ≤ v_c + 1` is false from 14
vertices on.

**Formalization.** `OpenProblem/WOWII348.lean` contains two theorems.
`WOWII348.conjecture348` gives `2|X| + 2 ≤ 3 γ_t` for trees on at least two vertices.
`conjecture348_real` is the stated real inequality. Both use Mathlib only and depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. The edge count is shared with the 372 proof as
`WOWII372.card_noneIn_le`.

## WOWII 377: proved

> If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ number of isolates of <M> + upper median(T)`.

The invariants:

- `M` is the set of vertices of maximum degree.
- The isolates of `<M>` are the maximum-degree vertices with no maximum-degree neighbour. Call
  this set `I`.
- The upper median is the entry at 0-based position `⌊n/2⌋` of the nondecreasing degree
  sequence.

WOWII lists this conjecture as open (dated February 2009).

**Proof.** Let `S` be a total dominating set.

- **The median is 1 or 2.** A tree has at least `2 + #(degree ≥ 3)` leaves, so fewer than half
  of its vertices have degree at least 3. The upper median is therefore 1 or 2, and it is 2
  exactly when at most half of the vertices are leaves.
- **`|I| + 1 ≤ |S|`, by edge counting.** Take:
  - one edge from each `v ∈ I ∩ S` to `S`;
  - all edges at each `v ∈ I - S`, at least two each;
  - one edge from each other vertex outside `S` to `S`.

  These edges are distinct because `I` is independent, and a tree has `n - 1` edges.
- **`|I| + 2 ≤ |S|` when at most half of the vertices are leaves.**
  - If the maximum degree is at least 3 and `|S| = |I| + 1`, the count is tight. Then `I ⊆ S`
    and every vertex outside `S` is a leaf, and a degree-sum count shows that more than half of
    the vertices are leaves.
  - If the maximum degree is 2, then `T` is a path, and `I` is empty unless `n = 3`.

Equality holds, for example, when the neighbours of one vertex are centres of stars of a larger
degree. The bound held with these exact definitions for all trees up to 17 vertices before the
proof was found (`experiments/trees_battery.cpp`).

**Formalization.** `WOWII377.conjecture377` in `OpenProblem/WOWII377.lean` uses Mathlib only and
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The upper median is
defined literally, as the entry at index `⌊n/2⌋` of `Multiset.sort` applied to the degree
multiset.

## WOWII 378: false

> If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ number of components of <M> + dist_avg(D_2(T))`.

Here `M` is the set of maximum-degree vertices and `D_2(T)` the set of degree-2 vertices.
WOWII does not define `dist_avg(S)` for a set `S`, and different sources read it differently, so
we refute the conjecture under four readings:

| Reading of `dist_avg(S)` | Counterexample | `γ_t` | components of `<M>` | `dist_avg(D_2)` |
| --- | --- | --- | --- | --- |
| mean over ordered pairs of distinct vertices of `S` | `T9` | 4 | 2 | 8/3 |
| mean of `d(v, S)` over all `v` | `T5` | 2 | 1 | 6/5 |
| mean of `d(v, S)` over `v ∉ S` (the tracker's reading for 363) | `T5` | 2 | 1 | 3/2 |
| mean of `d(s, v)` over `s ∈ S`, `v ≠ s` | `T5` | 2 | 1 | 3/2 |

The two counterexamples:

- `T9` is the path `5-0-7-2-8-1-6` with an extra leaf at `7` and at `8`. It is the smallest
  counterexample for the pairs reading.
- `T5` is the spider with legs of lengths 1, 1 and 2.

No tree with at most 15 vertices fails all four readings at once.

The neighbouring conjectures 356 and 374 also fail on trees with 3 or 4 vertices under the pairs
reading, which suggests that this batch of conjectures was generated from a database without
those trees.

**Formalization.** `OpenProblem/WOWII378.lean` proves `¬ Conjecture378 avg` for each of the four
readings: `distAvgPairs`, `distAvgToSet`, `distAvgToSetPos` and `distAvgFrom`. Each proof checks
the following facts about a concrete tree:

- that it is a tree;
- its degrees;
- a total dominating set;
- two separate components of `<M>`;
- lower bounds on distances.

All four theorems depend only on the standard axioms.

## WOWII 367: resolved

> If `T` is a tree on `n > 2` vertices such that the most frequently occurring degree is two, then
> `γ_t(T) ≥ (4/3) dd(T)`.

Here `dd` is the number of distinct degrees. The answer depends on how "the most frequently
occurring degree" is read.

- **Strict mode: true.** If degree 2 occurs strictly more often than every other degree, the bound
  holds. We prove `4 dd(T) ≤ 3 γ_t(T)` assuming only that there are more vertices of degree 2 than
  leaves.
- **Ties allowed: false.** The 12-vertex tree `K????B?KCWKW` has five leaves, five vertices of
  degree 2, one vertex of degree 3 and one of degree 4. So `dd = 4`, but `γ_t = 5 < 16/3`.

**Proof (strict mode).** Let `S` be a total dominating set and `m` the number of distinct degrees
that are at least 3. The proof combines two counts.

- **Edge count.** Take one edge from each vertex of `S` to `S`; these give at least `⌈|S|/2⌉`
  edges. Take one edge from each vertex outside `S` to `S`. Take a second edge at each non-leaf
  outside `S`; each such edge is counted at most twice. These edges are distinct, so
  `#non-leaves + 2 ≤ |S| + 2⌊|S|/2⌋`. This refines the Chellali–Haynes bound
  `γ_t ≥ (n − ℓ + 2)/2` when `|S|` is odd, and the case of four distinct degrees needs that
  refinement.
- **Leaf count.** The degree sum gives `ℓ = 2 + ∑_{deg v ≥ 3} (deg v − 2)`. The `m` distinct
  degrees that are at least 3 contribute at least `1 + 2 + ... + m`.

Since `n₂ > ℓ`, we get `#non-leaves ≥ 3 + m + m(m+1)/2`. Comparing this with the edge count
gives `3γ_t ≥ 4(m + 2) ≥ 4 dd`.

**Formalization.** `OpenProblem/WOWII367.lean` contains three theorems:

- `conjecture367`: `4 dd ≤ 3 γ_t` when `n₁ < n₂`;
- `conjecture367_real`: the stated real form, with the strict-mode hypothesis;
- `not_conjecture367_ties`: the tie-allowing reading is false, checked on the 12-vertex tree.

All three depend only on the standard axioms.

## WOWII 326: proved

> Let `G` be a simple connected graph with `n > 1`. If `3 μ(G) ≤ |E(S)|`, where `S` is the set of
> vertices of degree two, then `G` is well totally dominated.

Here `μ` is the matching number, `E(S)` is the set of edges joining two degree-2 vertices, and a
graph is well totally dominated when all its minimal total dominating sets have the same size.

**Proof.** The hypothesis forces `G = K₃`. Let `M` be a maximum matching.

- **Every `E(S)`-edge meets `M`.** Otherwise `M` could be enlarged.
- **Each `uv ∈ M` meets at most three `E(S)`-edges.** Equality holds only if `u` and `v` have
  degree 2 and all edges at `u` and `v` lie in `E(S)`.
- **So every `uv ∈ M` meets exactly three.** Combined with `3|M| ≤ |E(S)|`, the bound must be
  tight for each `uv ∈ M`.

Fix `uv ∈ M`, and let `x` and `y` be the other neighbours of `u` and `v`.

- Neither `x` nor `y` is covered by `M`. If `xz ∈ M`, it would also have to meet all three edges
  at `x` and `z`, including `ux`, which already belongs to `uv`.
- If `x ≠ y`, then `x-u-v-y` is an augmenting path, which is impossible.
- So `x = y`, and `u, v, x` is a triangle of degree-2 vertices, which is all of `G`.

The triangle is well totally dominated, since all its minimal total dominating sets have two
vertices. An exhaustive check found that the hypothesis holds only for `K₃` among all connected
graphs up to 9 vertices.

**Formalization.** `WOWII326.conjecture326` in `OpenProblem/WOWII326.lean` defines matchings,
minimal total dominating sets and well total domination directly. It depends only on the standard
axioms.

The related conjectures 318, 319, 320, 321, 324, 325 and 328 also hold for all connected graphs up
to 9 vertices. For 321, the hypothesis `ecc_avg ≥ Tdist_max/3` forces at most 7 vertices, so it
reduces to a finite check, but we have not formalized that check.

## WOWII 358 and 359: false

> **358.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ ½ ecc(C) + number of isolates of <S(T)>`.

> **359.** If `T` is a tree on `n > 2` vertices, then
> `γ_t(T) ≥ ½ ecc(C) + number of components of <S(T) ∪ L>`.

Here `C` is the center, `S(T)` the set of support vertices and `L` the set of leaves. Each
isolated support vertex together with its leaves is a component of `<S(T) ∪ L>`, so a
counterexample to 358 is also one to 359.

**Set eccentricity, `ecc(C) = max_v d(v, C)`.** This is the convention formal-conjectures uses
for WOWII.

- The counterexample is the 19-vertex tree with spine
  `3-13-2-17-11-0-15-6-16-1-12-18-4-14-5` and pendant leaves at `17, 15, 16, 18`.
- Its center is `{6}` with `ecc(C) = 7`, it has six pairwise non-adjacent supports, and
  `γ_t = 9 < 7/2 + 6`.
- It is the only counterexample with at most 19 vertices: all trees up to 19 vertices were
  checked.

The construction behind it: take a path and attach leaves at positions `5j+1` and `5j+3`. Then
`{5j+1, 5j+2, 5j+3}` is a total dominating set of size `3m` with `2m` isolated supports, while
`½ ecc(C) ≈ 5m/4`. The gap grows linearly; for example, at 205 vertices `γ_t = 89 < 95.5`. A
random search over trees with at most 60 vertices had missed this family.

**Radius, `ecc(C)` = eccentricity of a center vertex.** The 12-vertex tree with spine
`2-8-1-10-0-7-11-3-9-4` and leaves at `10, 11` has radius 5 and four isolated supports, and
`γ_t = 6 < 5/2 + 4`.

**Formalization.** `OpenProblem/WOWII358.lean` contains `not_conjecture358`,
`not_conjecture359`, `not_conjecture358_rad` and `not_conjecture359_rad`. The checks use:

- a path in a tree realises the distance between its ends;
- explicit walks bound the eccentricity of `6`;
- the triangle inequality bounds `d(3, c)` for every center `c`;
- decided total dominating sets and support sets.

All four theorems depend only on the standard axioms.

## WOWII 380 and 241: proved

> **380.** If `T` is a tree on `n > 2` vertices, then `γ_t(T) ≥ |D_even(T)| / (ecc(C) - 1)`, where
> `C` is the center and `D_even(T)` is the set of vertices of even degree.

> **241.** If `G` is a tree, then `γ_t(G) ≥ FLOOR[number of components(<N[S]>) + dist_avg(C)]`,
> where `S` is the set of degree-2 vertices and `C` is the center.

Both are listed as open (241 since 2007, 380 since 2009). We prove 380 under two readings of
`ecc(C)`: the eccentricity `max_v d(v, C)` of the set `C`, and the eccentricity of a center vertex
(the radius). We prove 241 with `dist_avg(C)` the mean distance between distinct center vertices,
by analogy with `dist_avg(V)`.

**Tree facts used.**

- **Centers are equal or adjacent.** Suppose two center vertices `c, c'` are at distance at
  least 2, and let `m` be the second vertex of the path from `c` to `c'`. Every path from a vertex
  to `c` or to `c'` passes through `m`, so `m` has smaller eccentricity. This is a contradiction.
- **Non-leaves versus total dominating sets.** Every tree satisfies `#non-leaves ≤ 2γ_t − 2`.
  This follows from the WOWII 367 edge count.

  If every vertex lies within distance 2 of the center, the bound improves to
  `#non-leaves ≤ γ_t`. In that case every non-leaf outside the center is a support vertex, and
  short-cycle arguments (every tree edge is a bridge) give an injection from the non-leaves
  outside `S` into the leaves inside `S`.
- **Components of `<N[A]>`.** For any vertex set `A`, the subgraph `<N[A]>` has at most `γ_t − 1`
  components. Each component contains a vertex of `S`. If each contained exactly one, those
  vertices would need neighbours in `S` outside `N[A]`.

**Proof of 380.** Every even-degree vertex is a non-leaf. Split on `e = ecc(C)`:

- If `e ≥ 3`, then `|D_even| ≤ 2γ_t − 2 ≤ (e − 1)γ_t`.
- If `e = 2`, the tree lies within distance 2 of its center, so `|D_even| ≤ γ_t`.
- If `e ≤ 1`, the right side is at most 0.

**Proof of 241.** Distinct centers are adjacent, so `dist_avg(C) ≤ 1`. The floor is therefore at
most `#components + 1 ≤ γ_t`.

The readings of `dist_avg(C)` as the mean distance to `C` (over all vertices, or over non-centers)
also held for all trees up to 16 vertices, but we have not proved them.

**Formalization.** `OpenProblem/WOWII380.lean` contains `conjecture380`, `conjecture380_rad` and
`conjecture241`, together with the reusable `center_adj` and `nonleaves_le_of_near`. All depend
only on the standard axioms.

## WOWII 372: proved

> If `T` is a tree on `n > 2` vertices, then `γ_t(T) ≥ v_c(T) / (p(T) - 1)`.

The invariants:

- `γ_t` is the total domination number.
- `v_c` is the vertex cover number.
- `p` is the path covering number.

For a path, `p = 1` and the right side divides by zero. The real content is therefore
`v_c ≤ (p - 1) γ_t` when `p ≥ 2`.

The page notes that `p ≥ 3` follows from the bound `γ_t ≥ (2/3)(v_c + 1)`, quoted from a 2009
preprint of DeLaViña, Larson, Pepper and Waller. That left the case `p = 2` open.

**Proof.** Let `S` be a minimum total dominating set.

- `p ≥ 3`, by edge counting. A tree has `n - 1` edges. At least `n - |S|` edges join `S` to the
  rest, and at least `|S|/2` edges lie inside `S`. So at most `|S|/2 - 1` edges avoid `S`.
  Then `S`, plus one end of each such edge, is a vertex cover. Hence `2 v_c + 2 ≤ 3 γ_t`.
- `p = 2`. A tree covered by two vertex-disjoint paths is exactly those two paths `P` and `Q`
  plus one edge `f i — g j`, because it has `n - 1` edges and the paths contribute `n - 2`.
  - A vertex cover: one parity class of each path, plus possibly one vertex. Its size is
    `⌊a/2⌋ + ⌊b/2⌋ + [a, b odd and i, j even]`, with 0-indexed positions.
  - A matching lower bound for every total dominating set. Each vertex of a path has at most
    two neighbours on it, so dominating `m` path vertices needs at least `⌈m/2⌉` of them.
    When `f i` is dominated only by `g j`, split `P` at `i` to gain the extra one.

Checked by computer for all trees up to 23 vertices (14.8 million at `n = 23`).

**Formalization.** `OpenProblem/WOWII372.lean` contains two theorems. `conjecture372` gives
`v_c ≤ (p - 1) γ_t` when `p ≥ 2`. `conjecture372_real` is the stated real inequality, using the
convention `x / 0 = 0`. Both use Mathlib only and depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The path cover definition is copied from formal-conjectures
(`IsPathCover`).


## Other targets examined (still open)

### WOWII 133 (open in formal-conjectures)

The statement is `path(G) ≥ rad(G) + avg_v λ(v)` when `G` has no 4-cycle, and
`path(G) ≥ rad(G) + 1` otherwise. The 4-cycle case is easy: a diametral path is induced.

Evidence for the C4-free case:

- It holds for every connected C4-free graph with at most 14 vertices (`c133.cpp`).
- The minimum slack for 7 ≤ n ≤ 14 is exactly `2/n`, attained by stars.
- Equality holds for `K2`, `K3`, `C5`, `C6` and the Petersen graph.
- The theta graphs θ(3, k) have slack `3/(k+1)`, which tends to 0.
- It holds for all cubic and 4-regular graphs with girth ≥ 5 up to 21 vertices, and for all
  graphs with girth ≥ 5 and minimum degree ≥ 2 up to 16 vertices.
- It holds for polarity graphs, where induced paths are far longer than needed, and for
  generalized Petersen graphs and cages.

Proved partial case: if `avg λ ≤ 2` the inequality holds. Indeed `path ≥ rad + 1` always. If
some `v` has `λ(v) ≥ 2`, a geodesic from `v` to a farthest vertex extends at `v` by a neighbour
not adjacent to the geodesic's second vertex, giving `path ≥ ecc(v) + 2 ≥ rad + 2`. In a
C4-free graph that neighbour cannot be adjacent to the geodesic's third vertex.

### WOWII 61 (open in formal-conjectures)

The statement is `f(G) ≥ res(G) + ⌈diam/3⌉`, where `f` is the order of a largest induced forest
and `res` is the Havel–Hakimi residue. It holds for all connected graphs up to 10 vertices.

The variant with `α` in place of `res` is false. The smallest counterexample is the graph6 graph
`E?zO`, with `f = 5`, `α = 4`, `res = 3` and `diam = 4`. So any proof must use the residue.

A related construction holds up to 9 vertices: a set `X` of vertices pairwise at distance ≥ 3 with
`|X| ≥ ⌈D/3⌉` and `|X| + α(G − X) ≥ res + ⌈D/3⌉`. Note that `X ∪ J` is an induced forest for
every independent `J`. The residue-only version of this construction fails twice at 9 vertices.

### TxGraffiti Conjecture 3 (open)

The statement is `i(G) ≤ μ*(G) = γ_e(G)` for every regular `G`.

Exhaustive checks found no counterexample among:

- connected cubic graphs with at most 20 vertices;
- connected 4-regular graphs with at most 15 vertices;
- connected 5-regular graphs with at most 12 vertices;
- about 340 graphs from structured families (generalized Petersen graphs, prisms, Möbius ladders,
  circulants, tori, line graphs and named cubic graphs).

Equality is common, for example `GP(5k, 2)`, `K_{r,r}` and `C5[K̄_t]`.

Gupta's 50-vertex graph has `γ = 14 < γ_e = 15` and no dominating transversal (arXiv
2608.22498). It satisfies `i = γ_e = 15` (ILP, `relax.py`). The witness skips the three
variables of one gadget and uses its complementary pair of clauses.

For the incidence graph of a balanced 3-SAT formula (3 literals per clause, each literal twice):

- `i − #vars` equals the minimum of `|W| − |K|` over relaxations (`relax.py`).
- Every OR-gadget with 3 local variables has relaxation profile `(−1, 0, 0, 1)`. A counting
  argument then shows that skeletons built only from such gadgets always admit a relaxation of
  cost ≤ 0.
- Random walks over unsatisfiable formulas with 15 and 18 variables, and annealing over formulas
  and cubic graphs, found nothing better than `i = γ_e`.

### Further untouched WOWII conjectures

These were tested with standard invariant readings (`test1.cpp`, `big.cpp`): 84, 161, 165, 174,
179, 199, 247, 255, 256, 281, 300, 384b, 387, 392b, 392c, 394, 422a, 422b, 422c, 426 and 434e.
None failed on about 143,000 random graphs with 10–15 vertices. All but 161, 165, 255, 256, 281,
300 and 434e were also checked on every connected graph with at most 10 vertices (11,716,571
graphs at `n = 10`); those seven were checked exhaustively up to 9 vertices.

- Other tree conjectures of this batch were tested with all trees up to 17 vertices and 20,000
  random trees with at most 60 vertices (`experiments/trees_battery.cpp`):
  - 242, 342, 343, 344 and 356 (distance-to-set reading) show no counterexample.
  - 374 and 375 fail on trees with 3 to 5 vertices under every reading of `B`, `dist_avg` and
    the median that we tried. This points to a transcription problem, so we do not claim them.
- WOWII 174 (`L_s + b ≥ n + max λ - 1`, Conjecture 3 of DeLaViña–Waller 2008) and
  WOWII 177 (`L_s + b ≥ 2α + σ`, where `σ` is the second-smallest degree) hold for all connected
  graphs up to 9 vertices. Both have many equality cases, such as `C5` with pendants at one
  vertex. A targeted search of 20,000 spiders with mixed-parity legs plus vertices closing
  5-cycles found no counterexample to 174.
- The Hamiltonian-path conditions 189, 190 and 213 hold for all connected graphs up to 9
  vertices. For 189 this uses `dist_even(v)` counting `v` itself; the other reading already fails
  on `K_{1,3}`.
