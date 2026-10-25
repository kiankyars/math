# Graffiti-type graph conjectures: notes

Status, all verified in Lean:

- **Proved:** WOWII 96, 161, 162, 169, 178, 179, 241, 310, 318, 320, 321, 323, 325, 326, 348,
  361, 372, 377, 380, 426, 434b, 434c, 435, 436c, 438a and 449. (For 361 the tracker cites an
  informal manuscript proof; see its section.)
- **Refuted:** WOWII 174, 255, 256, 267, 281, 300, 319, 328, 358, 359, 378, 393d, 394, 399b, 402,
  422b, 425d, 425e, 427, 439, 442 and 444. (174 is also Conjecture 3 of DeLaViña–Waller, EJC
  2008.) (427 leaves `C` undefined; one tree refutes both
  readings, `C` the centre and `C = M`.)
- **False as stated:** WOWII 382b, 391, 399a, 401b and 412f. These fail on very small graphs
  (`K_3`, complete graphs, stars and a 5-vertex spider), which suggests transcription problems;
  see their sections.
- **Resolved both ways:**
  - WOWII 367 is true when degree 2 is a strict mode and false when ties are allowed.
  - WOWII 434a is true when its undefined `M` is the set of maximum degree vertices, and false
    when `|M|` is read as the number of pendants (the set `P` that the statement defines).

The files are `OpenProblem/WOWII96.lean`, `WOWII161.lean`, `WOWII162.lean`, `WOWII169.lean`, `WOWII174.lean`, `WOWII178.lean`, `WOWII179.lean`, `WOWII255.lean`, `WOWII256.lean`, `WOWII267.lean`, `WOWII281.lean`, `WOWII300.lean`, `WOWII310.lean`, `WOWII318.lean`, `WOWII319.lean`, `WOWII320.lean`, `WOWII321.lean`, `WOWII323.lean`, `WOWII325.lean`, `WOWII326.lean`, `WOWII328.lean`, `WOWII241`/`WOWII380` (both in
`OpenProblem/WOWII380.lean`), `WOWII348.lean`, `WOWII358.lean` (358 and 359), `WOWII361.lean`, `WOWII382b.lean`, `WOWII391.lean`, `WOWII393d.lean`, `WOWII394.lean`, `WOWII399a.lean`, `WOWII399b.lean`, `WOWII401b.lean`, `WOWII402.lean`, `WOWII412f.lean`, `WOWII422b.lean`, `WOWII425d.lean`, `WOWII425e.lean`, `WOWII426.lean`, `WOWII427.lean`, `WOWII434.lean` (434a, 434b and 434c), `WOWII435.lean`, `WOWII436c.lean`, `WOWII438a.lean`, `WOWII439.lean`, `WOWII442.lean`, `WOWII444.lean`, `WOWII449.lean`, `WOWII367.lean`, `WOWII372.lean`,
`WOWII377.lean` and `WOWII378.lean`.

The other conjectures below are still open. For them we record evidence and partial results only.

Source of statuses: E. DeLaViña, *Written on the Wall II* (WOWII), through the JSON
transcription of the archived "open" page, cross-checked in October 2026 against the issue
tracker of google-deepmind/formal-conjectures. Some WOWII conjectures have recently been
resolved there by other contributors, so we only claim numbers with no activity on that tracker.

## WOWII 174: false (DeLaViña–Waller Conjecture 3)

> If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ n + max_v λ(v) - 1`.

This is Conjecture 3 (Graffiti.pc 174) of E. DeLaViña and B. Waller, *Spanning trees with many
leaves and average distance*, Electron. J. Combin. 15 (2008), #R33: `L ≥ n - b + µ - 1`. Here
`µ` is the local independence number. The paper proves the weaker bounds `L ≥ n - b + 1` and
`L ≥ n - b + ⌈µ/2⌉`.

**Counterexample.** The graph `J{Thg_@?G__` on 11 vertices. The vertex `3` is a cut vertex.

- `A = {0, 1, 2, 4, 5, 6}` is a 3-sun: a triangle `1, 2, 5` whose edges are capped by `0`, `4`
  and `6`. The vertex `3` is adjacent to the three caps.
- `3 - 7 - 8 - 9 - 10 - 3` is a 5-cycle.

Then:

- `µ ≥ λ(3) = 5`.
- `b = 8`. The four triangles of the sun need two deletions and the 5-cycle a third.
- `L_s = 6`. Every connected dominating set contains `3`, at least two vertices of `A` (to
  dominate `1, 2, 5` while staying connected to `3`), and at least two of `7, ..., 10`.

So `L_s + b = 14 < 15 = n + µ - 1`. Gluing `s` suns and `c` pentagons at the cut vertex gives
`L_s + b = n + µ - 1 - s` (for `c ≥ 1`), so the gap is unbounded. Two examples:

- `L{Thg_@?W`?FCD` has two suns and 13 vertices.
- The 17-vertex graph with `s = 2`, `c = 1` has gap 2.

The conjecture holds for all connected graphs with at most 10 vertices, so 11 is the minimum
order. Earlier annealing up to 20 vertices had missed this example. A prover agent found it by
reducing the conjecture to rooted pieces glued at a cut vertex. We recomputed it independently
twice: with `experiments/n10d.cpp` and with a Python brute force. 174 has no activity on the
formal-conjectures tracker (checked October 25, 2026), and we found no published refutation.

**Formalization.** `WOWII174.not_conjecture174` in `OpenProblem/WOWII174.lean` depends only on
the standard axioms. It uses the definitions of `L_s`, `b` and `λ` from
`OpenProblem/WOWII178.lean`. The bound `L_s ≤ 6` is proved from spanning trees directly:
- the internal vertices dominate;
- a tree path between two internal vertices has only internal vertices, so it crosses each cut
  at `3` along an edge between internal vertices.

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

*Later activity elsewhere (October 21, 2026):* after this work was committed, formal-conjectures
issue #7510 and pull request #7512 (J. J. Gebendorfer) proposed the same stronger bound
`2|X| + 2 ≤ 3|D|` for every total dominating set `D`, with a Lean proof. The PR was open when
checked.

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

*Later activity elsewhere (October 21, 2026):* after this work was committed, formal-conjectures
issue #7509 (J. J. Gebendorfer) reached the same split. It refutes the tied-mode reading with
`P_4` (degrees `1, 2, 2, 1`) and gives a written proof of a stronger bound for the unique-mode
reading. Pull request #7513 (same author, open when checked) later added a Lean proof of both
parts.

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

## WOWII 161: proved

> If `G` is a simple connected graph, then `L_s(G) ≥ maximum of λ(v) of Ḡ`.

Here `λ(v)` computed in the complement `Ḡ` is `α(Ḡ[N_Ḡ(v)])`, which is the order of a largest
clique of `G` made of vertices not adjacent to `v` (and different from `v`). WOWII lists this
conjecture as open.

**Proof.** Let `K` be a clique of `G` avoiding `N[v]`. Because `G` is connected and `v ∉ K`, some
`x ∈ K` has a neighbour `y ∉ K`. Then `deg x ≥ (|K| − 1) + 1 = |K|`. The star at `x` is acyclic, so
it extends to a spanning tree `T`. The degree sum `∑ deg_T = 2n − 2` gives
`deg_T x ≤ #leaves(T)`, hence `L_s ≥ deg x ≥ |K|`.

**Formalization.** `WOWII161.conjecture161` in `OpenProblem/WOWII161.lean` (with the helper
`degree_le_Ls`: `deg x ≤ L_s` for every vertex) depends only on the standard axioms.

## WOWII 162: proved

> If `G` is a simple connected graph, then `L_s(G) ≥ freq of minimum of λ(v) · ⌊1/δ(G)⌋`.

The factor `⌊1/δ⌋` is `1` when `δ = 1` and `0` otherwise. So the content is: if `δ = 1`, then
`L_s` is at least the number of vertices at which `λ(v) = α(G[N(v)])` is minimal. WOWII lists
this conjecture as open (August 2005).

**Proof.**

- A vertex of degree one has `λ = 1`, so each minimiser `v` of `λ` has `λ(v) ≤ 1`. Its
  neighbourhood is then a clique: `v` is simplicial.
- **Lemma.** If every vertex of `S` is simplicial and has a neighbour outside `S`, then
  `L_s ≥ |S|`. Attach each `v ∈ S` to one neighbour `p(v) ∉ S`, and keep the edges of `G` with
  both ends outside `S`. This spanning subgraph `H` is connected. For an edge `ab` of `G`:
  - with `a ∈ S`, `b ∉ S`, use `a – p(a) – b`, since `p(a)` and `b` are adjacent neighbours of the
    simplicial vertex `a`;
  - with both ends in `S`, use `a – p(a)`, then the previous case for `b` and `p(a)`.
  
  Every vertex of `S` has degree 1 in `H`, so it is a leaf of any spanning tree of `H`.
- If some minimiser `v` has all its neighbours among the minimisers, then `N[v]` is closed under
  adjacency, so `v` is universal. Being simplicial, it makes `G` complete. With `δ = 1` this
  forces `n = 2`, where both sides equal 2.

**Formalization.** `WOWII162.conjecture162` in `OpenProblem/WOWII162.lean` depends only on the
standard axioms. The general lemma is `card_le_Ls_of_simplicial`.

## WOWII 310: proved

> If `G` is a simple connected graph with `n > 2`, then `γ_t(G) ≤ ⌈1 + Tdist_min / 3⌉`.

Here `Tdist(v) = ∑_u d(v, u)`. WOWII lists this conjecture as open.

We prove `3 γ_t ≤ Tdist(v) + 5` for **every** vertex `v`, which is equivalent to
`γ_t ≤ 1 + ⌈Tdist(v) / 3⌉`.

**Proof.**

- If `v` is adjacent to all other vertices, `{v, w}` for any neighbour `w` is a total dominating
  set, and `Tdist(v) = n − 1 ≥ 1`.
- Otherwise some vertex is at distance exactly 2. Let `A`, `B`, `C` be the vertices at distance
  `1`, `2` and `≥ 3` from `v`. Give each vertex of `B ∪ C` a parent one step closer to `v`.
  - `{v} ∪ parents` is a total dominating set: `v` is dominated by the parent of a vertex of
    `B`, `A` by `v`, and `B ∪ C` by their parents.
  - The parents of `B` lie in `A`, so there are at most `min(|A|, |B|) + |C|` parents. This is
    at most `(|A| + 2|B| + 3|C|) / 3 ≤ Tdist(v) / 3`.

**Formalization.** `WOWII310.conjecture310` (with `three_mul_totalDomNum_le` for every vertex) in
`OpenProblem/WOWII310.lean` depends only on the standard axioms.

## WOWII 255: false

> If `G` is a simple connected graph, then `γ_t(G) ≥ 2|C| / max {|N(e)| : e ∈ E(G)}`, where `C`
> is the center of `G`.

WOWII lists this conjecture as open, and it has no activity on the formal-conjectures tracker
(checked October 21, 2026).

**Counterexample.** The 11-vertex graph has 20 edges:

- `c ~ ℓ₁, ℓ₂`;
- `ℓ₁` adjacent to independent vertices `a₁, …, a₄`, and `ℓ₂` adjacent to `b₁, …, b₄`, which form a
  clique;
- the matching `aᵢ ~ bᵢ`.

Any two vertices are adjacent or have a common neighbour, since `aᵢ` reaches `bⱼ` through `bᵢ`. No
vertex is universal, so every vertex has eccentricity 2 and `C = V`. Every edge has
`|N(e)| ≤ 7`, while `{c, ℓ₁, ℓ₂}` is a total dominating set. So `γ_t ≤ 3 < 22/7`.

The exhaustive search shows that no graph on at most 10 vertices is a counterexample, so this one
has the least possible order. More generally, any graph `H` on the `aᵢ`, together with its
complement on the `bᵢ`, gives diameter 2. With `p` vertices on each side the bound becomes
`2(2p + 3)/(p + 3) > 3` for every `p ≥ 4` (`experiments/c255.py`). The idea is the same as for 256:
the centre of a star in the total dominating set has small degree, while its leaves have large
private neighbourhoods. Here diameter 2 also puts every vertex in the centre.

**Formalization.** `WOWII255.not_conjecture255` in `OpenProblem/WOWII255.lean` depends only on the
standard axioms.

## WOWII 256: false

> If `G` is a simple connected graph, then `γ_t(G) ≥ 2|N(A)| / max {|N(e)| : e ∈ E(G)}`, where `A`
> is the set of vertices of minimum degree.

WOWII lists this conjecture as open, and it has no activity on the formal-conjectures tracker
(checked October 21, 2026). Exhaustive search up to 10 vertices and annealing up to 20 vertices
found no counterexample.

**Counterexample.** The 15-vertex graph has 20 edges:

- a vertex `c` adjacent to `ℓ₁` and `ℓ₂`;
- six further neighbours for each `ℓᵢ`, matched in pairs.

Every vertex other than `ℓ₁` and `ℓ₂` has degree 2. So `N(A) = V - {c}` and `|N(A)| = 14`. The
largest `|N(e)|` is 9, on `cℓᵢ`. But `{c, ℓ₁, ℓ₂}` is a total dominating set, so
`γ_t = 3 < 28/9`. Reading `N(A)` as the closed neighbourhood only enlarges the bound.

More generally, take `t` such vertices `ℓᵢ` with `p` matched private neighbours each. Then
`γ_t = t + 1`, `|N(A)| = t(p + 1)` and `max |N(e)| = t + p + 1`. The bound fails when
`(t + 1)(t + p + 1) < 2t(p + 1)`, for example for `t = 2, p ≥ 6` and `t = 3, p ≥ 6`.

The construction exploits the weakness of the general bound `γ_t · max |N(e)| ≥ 2n`: a star in
the total dominating set whose leaves have many private neighbours. Annealing found no smaller
counterexample on 11 to 14 vertices (`experiments/c256.py`).

**Formalization.** `WOWII256.not_conjecture256` in `OpenProblem/WOWII256.lean` depends only on the
standard axioms.

## WOWII 267: false

> If `G` is a simple connected graph with `girth(G) ≥ 5`, then `γ_t(G) ≥ ⌈dist_avg(A, V)⌉`,
> where `A` is the set of minimum degree vertices.

WOWII lists this conjecture as open. We read `dist_avg(A, V)` as the mean of `d(a, v)` over
`a ∈ A` and `v ∈ V`, either including the zero terms `v = a` or excluding them.

**Trees.** Trees already violate the conjecture if they count as having girth `∞`. The double
star with 3 and 4 leaves (`H???F?^`) has `γ_t = 2` but `dist_avg(A, V) = 43/21`. Trees are the
only violations with at most 13 vertices among graphs of girth at least 5
(`experiments/t302.cpp`).

**A cyclic counterexample.** Mathlib's `girth` is `0` for acyclic graphs, and under that
convention trees are excluded. The graph `G22` settles both conventions:

- the path `0 – 1 – 2 – 3 – 4 – 5`;
- the path `1 – 6 – 7 – 4`, which closes a 6-cycle without shortening any distance;
- seven leaves at `0` and seven leaves at `5`.

Its girth is 6, and `{0, 1, 4, 5}` is a total dominating set, so `γ_t ≤ 4`. The minimum degree
vertices are the 14 leaves, and the distances from each leaf sum to 89. So `dist_avg(A, V)` is
`1246/308 ≈ 4.05` including zero terms, or `1246/294 ≈ 4.24` excluding them. Either way its
ceiling is 5 > 4. This is the double broom with path length 5 and leaf count `k = 7`, the
smallest `k` that works (`experiments/c267.py`). The extra path is placed where the total
dominating set already dominates it.

**Formalization.** `OpenProblem/WOWII267.lean` contains four theorems, all depending only on the
standard axioms:

- `not_conjecture267`: girth in Mathlib's sense, mean including `v = a`;
- `not_conjecture267_pos`: girth in Mathlib's sense, mean over `v ≠ a`;
- `not_conjecture267_egirth`: Mathlib's `egirth` (trees allowed), mean including `v = a`;
- `not_conjecture267_egirth_pos`: `egirth`, mean over `v ≠ a`.

Distances are bounded below by functions that grow by at most one along each edge
(`le_add_dist`). Girth at least 5 follows from the absence of triangles and of two vertices with
two common neighbours (`five_le_egirth`).

## WOWII 300: false

> If `G` is a simple connected graph with `n > 2`, then
> `γ_t(G) ≤ (1/2)[n + frequency of λ_min(Ḡ)]`.

Here `λ_Ḡ(v) = α(Ḡ[N_Ḡ(v)])` is the order of a largest clique of `G` among the non-neighbours
of `v`. WOWII lists this conjecture as open.

**Counterexample.** `G12` has 12 vertices and 13 edges (graph6 `K{O`?CCA?@?D`):

- two triangles `{0, 1, 2}` and `{7, 8, 9}`, joined by the path `2 – 5 – 7`;
- a leaf `4` at `0`, the path `2 – 10 – 3`, and the path `1 – 11 – 6`.

Only `N[5]` meets both triangles. So `λ_Ḡ(5) = 2` and `λ_Ḡ(v) = 3` for every other `v`, the
frequency is 1, and the bound is `13/2`.

However `γ_t = 7`. Any total dominating set contains the supports `0`, `10` and `11`. It meets
`N(10) = {2, 3}` and `N(11) = {1, 6}`. It needs two of `5, 7, 8, 9`: vertices 8 and 9 force 7 or
both of 8 and 9, and 7 itself needs a neighbour.

**Search.** Exhaustive search finds no counterexample on connected graphs with at most 10
vertices (11,716,571 graphs at `n = 10`, `experiments/c300.cpp`). Simulated annealing finds many
counterexamples at `n = 12`.

**Formalization.** `WOWII300.not_conjecture300` in `OpenProblem/WOWII300.lean` depends only on the
standard axioms.

## WOWII 281: false

> If `G` is a simple connected graph with `n > 2`, then
> `γ_t(G) ≤ [frequency of λ_min(Ḡ)] + μ(G)`.

WOWII lists this conjecture as open. Here `μ` is the matching number, and `λ_Ḡ` is as in
WOWII 300.

**Counterexample.** `G13` has 13 vertices and 17 edges (graph6 `L}?gPGd?O@?@?C`). It is built from
a `K_4` on `{3, 5, 7, 10}` and a triangle `{0, 1, 9}`, with `0` and `1` also adjacent to `5`. Each
of `10`, `7` and `3` carries a pendant path of length 2: `10 – 2 – 12`, `7 – 4 – 8` and
`3 – 11 – 6`.

Only `N[5]` meets both `{0, 1, 9}` and `{3, 7, 10}`, so the frequency of `λ_min(Ḡ)` is 1. Since
`n` is odd, `μ ≤ 6`, so the bound is at most 7.

However `γ_t = 8`. A total dominating set contains:

- the supports `2`, `4` and `11`;
- a neighbour of each of these three supports;
- a neighbour `u ∈ {0, 1}` of `9`;
- a neighbour of `u`, which lies in `{0, 1, 5, 9}`.

These choices are pairwise distinct.

**Search.** The conjecture holds for all connected graphs up to 9 vertices. Simulated annealing
(`experiments/sagt.cpp`) finds counterexamples at `n = 13` and none at `n = 10, 11, 12`.

**Formalization.** `WOWII281.not_conjecture281` in `OpenProblem/WOWII281.lean` depends only on the
standard axioms.

## WOWII 382b: false as stated (only `K_3`)

> Let `G` be a connected graph on `n > 2` vertices. Then `γ_2 ≤ −1 + α(δ + |A_1|)`, where
> `A_1` is the set of vertices adjacent to exactly one vertex of non-minimum degree.

The triangle violates it: `γ_2(K_3) = 2`, `α = 1`, `δ = 2` and `A_1 = ∅`, so the right side is
`1`. The page itself observes that the remaining cases (`δ = 2`, `A_1 = ∅` or `δ = 1`,
`|A_1| = 1`) need `γ_2 ≤ 2α − 1`, which fails for `K_3`.

Among connected graphs with at most 9 vertices, `K_3` is the only counterexample
(`experiments/t382.cpp`). So this refutation probably points to a missing hypothesis such as
`n > 3`, and the version with `n > 3` is still open.

**Formalization.** `WOWII382b.not_conjecture382b` in `OpenProblem/WOWII382b.lean` depends only on
the standard axioms.

## WOWII 179: proved

> If `G` is a simple connected graph on at least 2 vertices, then
> `L_s(G) + b(G) ≥ Δ(G) + γ(G) + max λ(v)`.

WOWII lists this conjecture as open (August 2005).

**Proof.** The conjecture follows from two inequalities, each sharp for stars.

- `L_s ≥ Δ`, since a spanning tree containing every edge at a vertex `x` has at least `deg x`
  leaves.
- `b ≥ γ + λ(u)` for every vertex `u`. Let `J ⊆ N(u)` be independent with `|J| = λ(u)`, and let
  `I` be a maximal independent set of `G − J` containing `u`.
  - `I` dominates `G`: `u ∈ I` dominates `J`, and maximality handles the rest.
  - `I ∪ J` is a union of two disjoint independent sets, so it induces a bipartite subgraph.

  Hence `b ≥ |I| + |J| ≥ γ + λ(u)`.

**Formalization.** `WOWII179.conjecture179` in `OpenProblem/WOWII179.lean` depends only on the
standard axioms. The bound on `b` is `domNum_add_le_b`.

## WOWII 449: proved

> Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ |V \ H_3| + ⌈(|E(G[H_3])| − 1)/2⌉`, where `H_3` is the set of vertices of degree at
> least 3.

Here `α_2` is the 2-independence number: the largest set inducing maximum degree at most 1. WOWII
lists this conjecture as open (January 2012).

**Proof** (any finite graph). Let `S` be 2-independent, `L = V \ H_3`, and `A = S ∩ H_3`.

- Each `a ∈ A` has degree at least 3 and at most one neighbour in `S`, so it has at least two
  neighbours outside `S`.
- A vertex of `L \ S` has degree at most 2, so it receives at most two of these edges.
- The edges from `A` to `H_3 \ S` are distinct edges of `G[H_3]`.

Hence `2|A| ≤ 2|L \ S| + e(H_3)`, and so `|S| = |A| + |S ∩ L| ≤ |L| + ⌊e(H_3)/2⌋`. Finally,
`⌊e/2⌋ = ⌈(e − 1)/2⌉` for every `e ≥ 0`.

**Formalization.** `WOWII449.conjecture449` in `OpenProblem/WOWII449.lean` depends only on the
standard axioms.

## WOWII 442: false

> Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ n − ⌈path(G[H_3])/2⌉`.

WOWII lists this conjecture as open (January 2012).

**Counterexample.** The fan `F_{1,14}` is the path `0 – ⋯ – 13` plus a vertex adjacent to all of
it.

- The inner vertices `1, …, 12` have degree 3 and induce a path with 12 vertices (11 edges). So
  the bound is at most `15 − 6 = 9`, whether `path` counts vertices or edges.
- The set `{0, 1, 3, 4, 6, 7, 9, 10, 12, 13}` induces five disjoint edges, so `α_2 ≥ 10`.

In general `α_2(F_{1,p}) = ⌈2p/3⌉`. With `path` counting vertices, `F_{1,11}` (12 vertices) is
already a counterexample (`experiments/fan442.py`). The conjecture holds for all connected graphs
up to 9 vertices (`experiments/t449.cpp`, which also checks 444 and 449).

**Formalization.** `OpenProblem/WOWII442.lean` contains `not_conjecture442` (vertices) and
`not_conjecture442_length` (edges). Both depend only on the standard axioms.

## WOWII 444: false

> Let `G` be a connected graph on `n > 3` vertices. Then `α_2(G) ≤ n − ⌊dd(K_4(v))/2⌋`, where
> `dd(K_4(v))` is the number of distinct values of the number of `K_4` containing a vertex.

WOWII lists this conjecture as open (January 2012).

**Counterexample.** `G11` has 11 vertices and 28 edges and was found by simulated annealing
(`experiments/sa444.cpp`). The numbers of `K_4` at its vertices are 13, 12, 10, 5, 2, 9, 1, 4, 1,
7 and 0. That gives ten distinct values, so the bound is `11 − 5 = 6`. But
`{3, 4, 6, 7, 8, 9, 10}` induces a single edge, so `α_2 ≥ 7`.

The mechanism: a small dense core (here the clique `{0, 1, 2, 5}`) can give many
2-independent satellites pairwise distinct `K_4` counts. The conjecture holds for all connected
graphs up to 9 vertices, and annealing finds counterexamples at 11 vertices but not at 10.

**Formalization.** `WOWII444.not_conjecture444` in `OpenProblem/WOWII444.lean` depends only on the
standard axioms. The `K_4` counts are computed by `decide`.

## WOWII 401b: false as stated (stars)

> Let `G` be a connected graph on `n > 2` vertices. Then
> `γ_2 ≤ ⌊3·Tdist_max / freq[T_max(v)]⌋`.

`freq[T_max(v)]` counts the vertices maximising `T(v)`. We read `T(v)` either as the number of
triangles at `v` or as the total distance `Tdist(v)`.

Every star `K_{1,k}` with `k ≥ 6` refutes the conjecture under both readings. Its leaves all lie
in every 2-dominating set, so `γ_2 = k`. On the other hand `Tdist_max = 2k − 1`, and the
frequency is `k + 1` (no triangles) or `k` (the leaves maximise total distance), so the bound is
at most 5. For the triangle reading `K_{1,5}` already fails. Because it fails on stars, the
conjecture as transcribed probably differs from what Graffiti.pc produced.

**Formalization.** `OpenProblem/WOWII401b.lean` contains `not_conjecture401b_Tdist` and
`not_conjecture401b_numTri`, both for `K_{1,6}`. Both depend only on the standard axioms.

Other members of this batch that are clearly defined and have no tracker activity hold for all
connected graphs up to 9 vertices (`experiments/t4xx.cpp`): 395a, 421b, 421c, 422a, 422c and 438a
(426 has since been proved) (402 and 422b fail only at 12 and 14 vertices; see their sections).

## WOWII 394: false

> If `G` is a connected graph on `n > 2` vertices, then `γ_2 ≤ μ(G) + |E(G[A_2])| + |M|`,
> where `M` is the set of vertices of minimum local independence and `A_2` the set of degree-two
> vertices.

WOWII lists this conjecture as open (January 2010).

**Counterexample.** The graph has 12 vertices and 15 edges, found by simulated annealing
(`experiments/sa4.cpp`). It consists of a 4-cycle `3 – 1 – 5 – 2 – 3` with a leaf `4` at `5`,
and the edge `3 – 6` to the part `R = {0, 6, 7, 8, 9, 10, 11}`, whose edges are `0-6`, `0-7`,
`0-10`, `6-9`, `6-11`, `7-8`, `7-9`, `8-11` and `10-11`.

- `λ = 1` only at the leaf, so `|M| = 1`.
- The degree-two vertices `1, 2, 8, 9, 10` are independent, so `|E(G[A_2])| = 0`.
- `μ ≤ 5`: a perfect matching would match `4–5`, and then both `1` and `2` to `3`.
- `γ_2 ≥ 7`. A 2-dominating set contains `4`, and either both of `1, 2` or both of `3, 5`. It
  also contains at least four vertices of `R`, by a short case analysis on `8, 9, 10`, whose
  neighbourhoods are `{7, 11}`, `{6, 7}` and `{0, 11}`.

So `γ_2 = 7 > 6`. The conjecture holds for all connected graphs up to 9 vertices, and annealing
finds no counterexample on 11 or 13 vertices.

**Formalization.** `WOWII394.not_conjecture394` in `OpenProblem/WOWII394.lean` depends only on the
standard axioms.

## WOWII 402: false

> Let `G` be a connected graph on `n > 2` vertices. Then
> `γ_2 ≤ 2[isolates(G[A_δ]) + |{v : |N(v) ∩ A_Δ| = 1}| + γ_t]`.

WOWII lists this conjecture as open (January 2010).

**Counterexample.** The graph has 12 vertices and 32 edges and was found by simulated annealing
(`experiments/sa4.cpp`; edge list in `OpenProblem/WOWII402.lean`).

- The minimum degree 3 is attained only at the adjacent vertices `2` and `7`, so
  `isolates(G[A_δ]) = 0`.
- The maximum degree 7 is attained at `0, 1, 9, 10, 11`, and every vertex has zero or at least
  two neighbours among them.
- `{0, 1}` is a total dominating set.

So the bound is at most 4. A `decide` check over all quadruples of distinct vertices shows that no
four vertices 2-dominate, so `γ_2 ≥ 5` (in fact `γ_2 = 5`). Annealing finds no counterexample at
10 or 11 vertices.

**Formalization.** `WOWII402.not_conjecture402` in `OpenProblem/WOWII402.lean` depends only on the
standard axioms.

## WOWII 422b: false

> Let `G` be a connected graph on `n > 3` vertices and `M` its maximum degree vertices. Then
> `i(G) ≤ α(G[M]) + γ(G[V − M])²`.

WOWII lists this conjecture as open.

**Counterexample.** The graph has 14 vertices and 31 edges and was found by simulated annealing
(`experiments/sa4.cpp`, verified with `experiments/v402.py`).

- Vertex `1` is the unique vertex of maximum degree 8.
- `{0, 9}` dominates `G − 1`.

So the bound is at most `1 + 2² = 5`. But `i(G) = 6`. Let `I` be an independent dominating set.

- If `9 ∈ I`, then `I` avoids `N(9)`. This forces `2, 8, 12, 13` into `I` (all their neighbours
  lie in `N(9)`), together with one of the adjacent vertices `3` and `10`.
- If `9 ∉ I`, the leaf `4` lies in `I`, and the rest of `I` is an independent dominating set of
  `G − {4, 9}`. A `decide` check over all 4-tuples (repetitions allowed) shows that such a set has
  at least five vertices.

**Formalization.** `WOWII422b.not_conjecture422b` in `OpenProblem/WOWII422b.lean` depends only on
the standard axioms.

## WOWII 412f: false as stated

> Let `G` be a connected graph on `n > 2` vertices, `P` the set of pendants and `H` the union of all
> maximum critical independent sets. Then `|H| ≥ μ(G[V - N(P)])`, and if `G` is also bipartite,
> then `|H| ≥ c(G[V - N(P)]) + μ(G[V - N(P)])`.

The critical difference is the largest `|X| - |N(X)|` over all vertex sets `X` (Zhang; Larson).
An independent set is critical if it attains it. For `K_3`:

- `P = ∅`, so the right-hand side of the first clause is `μ(K_3) = 1`.
- The critical difference is `0`, attained by `∅`, while every single vertex gives `-1`.
- So `∅` is the only critical independent set, and `H = ∅`.

Hence the first clause fails. It also fails for every complete graph and every odd cycle. Since
Graffiti.pc's database contains these graphs, this points to a transcription problem.

The bipartite clause holds for all bipartite graphs up to 10 vertices, with bipartite annealing
up to 18. It is tight throughout and remains open. It does not follow from `|H| ≥ α`:
`α - c - μ` reaches `-3` on 10 vertices.

**Formalization.** `WOWII412f.not_conjecture412f` in `OpenProblem/WOWII412f.lean` depends only on
the standard axioms.

## WOWII 434b and 434c: proved

> **434b.** `i(G) ≤ δ(G[M]) + 1 + SW(Ḡ)`, and `i(G) ≤ δ(G[M]) + SW(Ḡ)` if the diameter exceeds 2.
> **434c.** `i(G) ≤ δ(G[V − M]) + 1 + SW(Ḡ)`, and `i(G) ≤ δ(G[V − M]) + SW(Ḡ)` if `δ(G) = 1`.

Here `M` is the set of maximum degree vertices, `i` is the independent domination number, and
`SW(H) = 1 + max_X δ(H[X])` is the Szekeres–Wilf number. WOWII lists both as open
(December 2010).

**Proof.** Both follow from `i(G) ≤ SW(Ḡ)`, because the extra terms are nonnegative and the side
conditions are not needed.

- Let `v` have maximum degree `Δ`. Then `v` together with a maximal independent set of
  `G − N[v]` is independent and dominating, so `i(G) ≤ n − Δ`.
- Taking `X = V` gives `SW(Ḡ) ≥ 1 + δ(Ḡ) = n − Δ`.

**434a** (`i(G) ≤ |M| + 2⌊SW(Ḡ)/2⌋`) defines the set `P` of pendants but uses an undefined
`M`. It has no activity on the formal-conjectures tracker (checked October 21, 2026).

- With `M` the set of maximum degree vertices, as in 434b and 434c, it holds:
  `i ≤ SW ≤ 1 + 2⌊SW/2⌋ ≤ |M| + 2⌊SW/2⌋` (`WOWII434.conjecture434a`).
- With `|M|` read as `|P|`, it fails for `K_4`. There `i = 1`, `P = ∅` and `SW(K̄_4) = 1`, so the
  bound is `0` (`WOWII434.not_conjecture434a_pendants`). For 434d and 434e, the bounds subtract `c(G[N[B]])` and `ecc(C)` respectively, so the
argument above is not enough. They hold for all connected graphs up to 9 vertices
(`experiments/t434.cpp`).

**Formalization.** `WOWII434.conjecture434b` and `conjecture434c` in `OpenProblem/WOWII434.lean`,
via `indepDomNum_le_SW`. Both depend only on the standard axioms.

## WOWII 438a: proved

> Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ a(G) + a(G[V - A]) + |E(G[A])|`, where `A` is the set of vertices of minimum degree.

Here `a` is the annihilation number: the largest `k` such that the `k` smallest degrees sum to at
most the number of edges. WOWII lists this conjecture as open (January 2012). It has no activity on
the formal-conjectures tracker (checked October 21, 2026); its sibling 438b was proved there.

**Proof.** We show `α_2(G) ≤ α(G) + α(G[V - A]) + |E(G[A])|` and then use Pepper's bound
`α ≤ a`, applied to `G` and to `G[V - A]`. Pepper's bound holds because the edges at an
independent set `S` are distinct, so the degrees of `S` sum to at most `|E|`.

Let `J` be 2-independent, so `G[J]` is a matching plus isolated vertices. Order the vertices with
those outside `A` last, and call a vertex of `J` *upper* if its neighbour in `J` comes earlier.

- The non-upper vertices of `J` form an independent set.
- The upper vertices outside `A` form an independent set of `G[V - A]`.
- An upper vertex in `A` has its neighbour in `J` in `A` too, since the vertices outside `A` come
  last. So these vertices give distinct edges of `G[A]`.

The intermediate bound holds on all connected graphs with 4 to 7 vertices, with equality in 8 of
them (`experiments/t438a.py`).

**Formalization.** `WOWII438a.conjecture438a` in `OpenProblem/WOWII438a.lean` depends only on the
standard axioms. Our `annihilation` maximises over vertex sets, which is equivalent to
formal-conjectures' definition by sub-multisets of the degree multiset.

## WOWII 391: false as stated

> If `G` is a connected graph on `n > 2` vertices, then `γ_2 ≤ p(G) + 1 + μ(G[T]) + |E(G[A_3])|`,
> where `T` is the set of vertices of degree two and `A_3` the set of vertices of degree at least
> three.

The transcription tags `p(G)` as the path cover number, as in 372, 407 and 418b. Take the spider
with legs of lengths 1, 1, 2 (5 vertices).

- The three leaves lie in every 2-dominating set, and the degree-2 vertex forces one more vertex,
  so `γ_2 = 4`.
- On the other side, `p = 2`, `T` is a single vertex and `A_3` is a single vertex, so the bound is
  `3`.

Reading `p(G)` as the number of pendants, the bound still fails on 561 connected graphs up to 9
vertices, the first on 8 vertices (`G?Bcr_`). It has no activity on the formal-conjectures tracker
(checked October 21, 2026). A failure on 5 vertices points to a transcription problem.

**Formalization.** `WOWII391.not_conjecture391` in `OpenProblem/WOWII391.lean` depends only on
the standard axioms.

## WOWII 427: false

> Let `G` be a connected graph on `n > 3` vertices and `M` the vertices of maximum degree. Then
> `i(G) ≤ |E(C, V - C)| + ⌊(2/3) |E(G[V - N(P)])|⌋`.

The statement never defines `C`. Its first sentence repeats the preamble of 422b, which suggests
`C = M`. Elsewhere in the list `C` is the centre. `P` is the set of pendant vertices, as in 412f.
One tree refutes both readings. It has 11 vertices and graph6 code `JqOI?C_G??_`:

- The centre `0` is adjacent to `1` and `7`.
- `1` is adjacent to the leaf `2` and starts the paths `1 - 3 - 4` and `1 - 5 - 6`.
- `7` is adjacent to the leaf `8` and starts the path `7 - 9 - 10`.

The leaves `2, 4, 6, 8, 10` have neighbours `1, 3, 5, 7, 9`. So `V - N(P)` spans no edge, and the
floor term is `0`.

- The centre is `{0}`, which meets 2 edges.
- `M = {1}`, which meets 4 edges.

So the bound is 2 under the first reading and 4 under the second. Every dominating set meets each
leaf–neighbour pair, so `i(G) ≥ 5`, and in fact `i(G) = 5`.

The centre reading already fails on 8 vertices (`G?`DB_`). The reading `C = M` holds for all
connected graphs up to 9 vertices. Two of the 106 trees on 10 vertices break it, and one of them is
the corona of the spider with legs 1, 1, 2.

Coronas give an infinite family. Let `H` be a connected graph with a unique vertex of maximum
degree `d`. In the corona of `H`, `i = |H|` while the bound is `d + 1`, so the bound fails whenever
`|H| ≥ d + 2`. 427 has no activity on the formal-conjectures tracker (checked October 21, 2026).

**Formalization.** `WOWII427.not_conjecture427` (centre) and `WOWII427.not_conjecture427M`
(`C = M`) in `OpenProblem/WOWII427.lean` depend only on the standard axioms.

## WOWII 393d: false

> If `G` is a connected graph on `n > 2` vertices, then
> `γ_2 ≤ μ(G[V − N(N(P))]) + α(G[V − M]) + |M_4|`.

Here `P` is the set of pendants, `M` the set of maximum degree vertices, and `M_4` the set of
vertices lying in the most copies of `K_4`. WOWII lists this conjecture as open. Conjectures
393a–c have tracker activity; 393d does not.

**Counterexample.** The graph has 12 vertices and 26 edges and was found by simulated annealing
(`experiments/sa5.cpp`, verified by `experiments/v393d.py`).

- The pendants `4` and `5` hang at `6` and `9`. So `V − N(N(P)) = {3, 6, 9, 11}`, which is
  independent, and `μ = 0` there.
- `M = {1, 2, 7, 10}`. The remaining eight vertices are covered by the edges `0-3`, `4-6`, `5-9`
  and `8-11`, so `α(G[V − M]) ≤ 4`.
- Only vertex `2` lies in four copies of `K_4`, so `|M_4| = 1`.

So the bound is at most 5, but `γ_2 = 6`. The pendants lie in every 2-dominating set, and a
`decide` check over all triples shows that no three further vertices complete one.

**Formalization.** `WOWII393d.not_conjecture393d` in `OpenProblem/WOWII393d.lean` depends only on
the standard axioms.

## WOWII 426: proved

> Let `G` be a connected graph on `n > 3` vertices and `M` the vertices of maximum degree. Then
> `i(G) ≤ n − γ(G[N(M)])`.

WOWII lists this conjecture as open (December 2010).

**Proof** (any finite graph, any set `M`). Let `J` be a maximal independent subset of `M`, and
extend it to a maximal independent set `I` of `G`, which is independent dominating. Then
`N(M) \ I` dominates `G[N(M)]`. If `x ∈ N(M) ∩ I` has a neighbour `m ∈ M`, then `m ∉ J`, because
`I` is independent. By maximality of `J`, `m` has a neighbour in `J ⊆ I`, so `m ∉ I` and
`m ∈ N(M)`. Hence `i(G) + γ(G[N(M)]) ≤ |I| + |N(M) \ I| ≤ n`.

**Formalization.** `WOWII426.conjecture426` in `OpenProblem/WOWII426.lean`, via
`indepDomNum_add_domNum_le`, depends only on the standard axioms.

## WOWII 425d: false

> Let `G` be a connected graph on `n > 3` vertices and `P` its set of pendants. Then
> `i(G) ≤ |T_min(G)| + Σ_v K_4(v) + γ(G[V − N(P)])`.

`T_min` is the set of vertices in the fewest triangles. WOWII lists this conjecture as open
(December 2010).

**Counterexample.** The graph has 12 vertices and 26 edges and was found by simulated annealing
(`experiments/sa6.cpp`, verified by `experiments/v425.py`). It has no pendants and no `K_4`, and
`{0, 7}` dominates it. Only vertex `2` lies in no triangle. So the bound is `1 + 0 + 2 = 3`.
A `decide` check over all triples shows that no independent set of at most three vertices
dominates, so `i(G) = 4`. Because there is no `K_4`, the result does not depend on how "sum of
`K_4(v)`" is read.

**Formalization.** `WOWII425d.not_conjecture425d` in `OpenProblem/WOWII425d.lean` depends only on
the standard axioms. In the same batch, 418b (with `p(G)` the path cover number) and 418c hold for
all connected graphs up to 9 vertices, and annealing found nothing for them
(`experiments/t418.cpp`).

## WOWII 328: false

> Let `G` be a simple connected graph with `n > 1`. If `4 μ(Ḡ) ≤` frequency of
> `max {K(v)}`, where `K(v)` is the number of `K_4` incident to `v`, then `G` is well totally
> dominated.

`μ` is the matching number. The frequency of the maximum is the number of vertices at which `K(v)`
is largest. `G` is well totally dominated if all its minimal total dominating sets have the same
size. WOWII lists this conjecture as open. It is not in formal-conjectures and has no activity on
its tracker (checked October 2026).

**Counterexample.** Simulated annealing found the graph (`experiments/saW.cpp`), and
`experiments/v328.py` verifies it with networkx. It has 10 vertices:

- vertices `0, …, 7` form a `K_8`;
- `8` and `9` are adjacent;
- `8` is joined to `1` and `4`, and `9` is joined to `2` and `6`.

The checks:

- Every edge of `Ḡ` contains `8` or `9`, so `μ(Ḡ) ≤ 2`.
- Each vertex of the `K_8` lies in `C(7, 3) = 35` copies of `K_4`, and `8` and `9` lie in none.
  So the maximum is attained `8 ≥ 4 μ(Ḡ)` times, and the hypothesis holds.
- `{1, 8}` and `{0, 3, 8, 9}` are both minimal total dominating sets, so `G` is not well totally
  dominated.

An exhaustive check over all connected graphs on at most 9 vertices (`experiments/e328.cpp` with
`nauty-geng`) finds no counterexample, so 10 vertices is the minimum.

**Formalization.** `WOWII328.not_conjecture328` in `OpenProblem/WOWII328.lean` depends only on
the standard axioms. The same annealing found no counterexample for the WTD conjectures 324
(residue reading) or 325, on 10, 12 and 14 vertices.

## WOWII 425e: false

> Let `G` be a connected graph on `n > 3` vertices and `D` the set of neighbor dominators of `G`.
> Then `i(G) ≤ 4|T_min(G)| + |E(G[D])|`.

DeLaViña and Pepper (*Graffiti.pc on the k-independence number of a graph*) call `v` a neighbor
dominator if `N[u] ⊆ N[v]` for some vertex `u ≠ v`. WOWII lists this conjecture as open
(December 2010). It has no activity on the formal-conjectures tracker (checked October 2026).

**Counterexample.** Simulated annealing found the graph (`experiments/sa9.cpp`, which computes `i`
by branching), and `experiments/v425e.py` verifies it by brute force. It has 12 vertices and
27 edges:

- No vertex is a neighbor dominator, so `|E(G[D])| = 0`.
- Vertex `10` lies in no triangle, and every other vertex lies in at least one, so
  `|T_min| = 1`.

So the bound is `4`, but `i(G) = 5`. Annealing finds many counterexamples on 12 to 24 vertices,
and an exhaustive search finds none on 10 or fewer vertices. Since `D = ∅`, the result does not
depend on how `D` is read, as long as `u ≠ v` is required.

**Formalization.** `WOWII425e.not_conjecture425e` in `OpenProblem/WOWII425e.lean` depends only on
the standard axioms. `i(G) ≥ 5` is a `decide` check over all quadruples.

In the same batch, annealing (`experiments/sa8.cpp`) on 8 to 14 vertices found no counterexample
for 399c, and an exhaustive check up to 8 vertices found none either. 439 is refuted below. 397c, 420b, 420c,
422d, 423, 430a and 433 were also searched but have tracker activity, so we make no claim about
them.

## WOWII 439: false

> Let `G` be a connected graph on `n > 3` vertices. Then `α_2(G) ≤ |N(M)| + ⌊2(CW(G) - 1)⌋`, where
> `M` is the set of maximum degree vertices and `CW(G)` is the Caro–Wei invariant of `G`.

`α_2` is the largest size of a set inducing maximum degree at most one, and
`CW(G) = ∑_v 1/(deg v + 1)`. WOWII lists this conjecture as open. It has no activity on the
formal-conjectures tracker (checked October 2026).

**Counterexample.** `experiments/sa10.cpp` computes `α_2` by branch and bound, and
`experiments/v439.py` verifies its result by brute force. The graph has 15 vertices and 26 edges:

- Vertices `0, …, 9` induce the perfect matching `01, 23, 45, 67, 89`, so `α_2 ≥ 10`.
- Vertices `10, …, 14` carry the other edges, and `14` is the only vertex of maximum degree `5`.
  So `|N(M)| = 5` under any reading of `N(M)`.
- The degrees are one `2`, seven `3`s, six `4`s and one `5`. So `CW = 69/20` and
  `⌊2(CW - 1)⌋ = 4`.

So the bound is `9 < 10`. The idea behind the construction: keep the large 2-independent set
outside the neighbourhood of a unique maximum-degree vertex, and give every vertex a fairly high
degree so that `CW` stays small. An exhaustive search finds no counterexample on 10 or fewer
vertices, and annealing finds none on 11 to 14.

**Formalization.** `WOWII439.not_conjecture439` in `OpenProblem/WOWII439.lean` depends only on the
standard axioms.

## WOWII 399a: false as stated (complete graphs)

> If `G` is a connected graph on `n > 2` vertices, then `γ_2 ≤ WP(Ḡ) + ⌊α(G[C])/2⌋`, where `C`
> is the center.

WOWII marks this "open, partial results known". Its note says that, since `γ_2 ≤ α_2 ≤ WP(Ḡ) + 1`,
it remains to settle `γ_2 ≤ WP(Ḡ)` when `α(G[C]) = 1`. That case fails for every complete graph
`K_n` with `n ≥ 3`: `γ_2(K_n) = 2`, while `WP(K̄_n) = 1` and `α(K_n) = 1`.

Graffiti.pc's database surely contains complete graphs, so this suggests a transcription problem,
as for 382b. `WOWII399a.not_conjecture399a` in `OpenProblem/WOWII399a.lean` refutes the printed
statement with the triangle, and depends only on the standard axioms.

## WOWII 399b: false

> If `G` is a connected graph on `n > 2` vertices, then `γ_2 ≤ WP(Ḡ) + ⌊3/α(G[A_3])⌋`, where
> `A_3` is the set of vertices of degree at least three.

`WP(H) = max_i min(d_i + 1, i)` is the Welsh–Powell number of `H`, with degrees in nonincreasing
order. WOWII lists this conjecture as open. It has no activity on the formal-conjectures tracker
(checked October 2026).

**Counterexample.** `experiments/sa11.cpp` found it, using branch and bound for `γ_2`, and
`experiments/v399b.py` verifies it by brute force. Vertices `4, …, 11` form a `K_8`, and the
independent vertices `0, 1, 2, 3` are attached by

  `N(0) = {4, 10}`, `N(1) = {5, 8, 11}`, `N(2) = {9, 10, 11}`, `N(3) = {6, 7, 11}`.

The checks:

- Only `0, 1, 2, 3` have at least four non-neighbours, so `WP(Ḡ) = 4`.
- `{1, 2, 3, 4} ⊆ A_3` is independent, so `⌊3/α(G[A_3])⌋ = 0`.
- `γ_2 = 5`: `{0, 1, 2, 3, 4}` 2-dominates. A vertex of `0, 1, 2, 3` outside a 2-dominating set
  needs two neighbours inside it, and no two of the sets `N(i)` share two vertices. So four vertices
  never suffice.

So the bound is `4 < 5`. An exhaustive search finds no counterexample on 9 or fewer vertices.

**Formalization.** `WOWII399b.not_conjecture399b` in `OpenProblem/WOWII399b.lean` depends only on
the standard axioms. `WP` is defined without sorting: it is the largest `k` such that at least `k`
vertices have degree at least `k - 1`, which equals `max_i min(d_i + 1, i)`.

**Related search.** In the same run, annealing up to 20 vertices found nothing for:

- `γ_2`: 382c, 382d, 387, 392b–f, 395a and 399c;
- `i`: 418c, 421b, 421c, 422a, 422c, 434d and 434e;
- `α_2`: 435 and 438a (both since proved);
- `γ_t`: 232, 233, 255, 256, 299, 302 and 304.

For 298 (`γ_t ≤ a(G) + χ_{C_4}(G)`) it found 12-vertex trees with `γ_t = a + 1`, but only because
`sa12.cpp` reads `χ_{C_4}` as "contains a 4-cycle". With the reading used below for 133 and 298
(`χ_{C_4} = 1` for C4-free graphs), the tree case is exactly the theorem `γ_t(T) ≤ a(T) + 1` of
Desormeaux, Haynes and Henning (2013). With the other reading the conjecture already fails on
`P_6`. Either way we make no claim about 298.

**More annealing with exact branch and bound** (`experiments/sa13.cpp`: `b`, `tree(G)` and `L_s`
via the connected domination number, all checked against brute force up to 8 vertices). Nothing
was found for:

- 72, 76, 84, 108, 111, 165, 166, 174, 180, 183 and 185, up to 20 vertices.
- 258, 259 and 260 (`γ_t ≥ 2X/L_s`, with `L(G) = L_s` as in formal-conjectures' 217, and `X` the
  largest even-distance count, `|N(M) - M|` or `|N(B) - B|`), up to 26 vertices. All three are
  tight on paths, cycles and stars. 261 was also tested, up to 20 vertices.
- 182, 184 and 186, with `B(G²)` the periphery of `G²` as in formal-conjectures' 181. We tried two
  readings of `Δ(B(G²))`, two of `dist_avg(B(G²), V)` and two of `N(C(G²))`, up to 18 vertices.
- 431c (`i ≤ residue · |T_max| + dd`), up to 24 vertices.

## WOWII 435: proved

> Let `G` be a connected graph on `n > 3` vertices. Then
> `α_2(G) ≤ SW(Ḡ) + ⌈(1 + |E(G²[A])|)/3⌉`, where `A` is the set of minimum degree vertices of `G²`.

WOWII lists this conjecture as open (January 2012). It has no activity on the formal-conjectures
tracker (checked October 2026). Earlier annealing found many equality cases but no counterexample.

**Proof.** We show `α_2(G) ≤ SW(Ḡ) + 1`. The ceiling is at least `1`, both in the printed reading
and in the reading `⌈1 + |E(G²[A])|/3⌉` (the source's brackets are unbalanced).

- Let `S` be a 2-independent set.
- Each `x ∈ S` has at most one neighbour in `S`, so in `Ḡ` it is adjacent to at least `|S| - 2`
  vertices of `S`.
- So `δ(Ḡ[S]) ≥ |S| - 2`, and `SW(Ḡ) = 1 + max_X δ(Ḡ[X]) ≥ |S| - 1`.

This is the Szekeres–Wilf analogue of the bound `α_k ≤ WP(Ḡ) + k - 1` of DeLaViña and Pepper
(2012). It is sharper, because `SW ≤ WP`. Connectivity and `n > 3` are not needed.

**Formalization.** `WOWII435.conjecture435` and `WOWII435.conjecture435'` in
`OpenProblem/WOWII435.lean` depend only on the standard axioms. The key lemma is
`WOWII435.twoIndepNum_le_SW`.

## WOWII 436c: proved

> Let `G` be a connected graph on `n > 3` vertices. Then `α_2(G) ≤ k · WP(Ḡ) + Δ(G[D])`, where
> `Δ(G[D])` is the maximum degree of the subgraph induced by the neighbor dominators and `k` is the
> `k`th step for a zero in the Havel–Hakimi process.

WOWII marks this conjecture "open, partial results known". DeLaViña and Pepper proved
`α_k ≤ WP(Ḡ) + k - 1`, and the WOWII note says it "simply remains to settle `α_2 ≤ WP(Ḡ)`
whenever the neighbor dominators are isolated in the subgraph that they induce and when `k = 1`".
We follow formal-conjectures' reading of `k` (their Conjecture 291): the least `i` such that the
list contains a zero after `i` Havel–Hakimi steps. It has no activity on the formal-conjectures
tracker (checked October 2026).

**The cases.**

- If `Δ(G[D]) ≥ 1` or `k ≥ 2`, the conjecture follows from `α_2 ≤ WP(Ḡ) + 1`. That bound holds
  because the `s` vertices of a 2-independent set have degree at least `s - 2` in `Ḡ`.
- If `k = 1`, the first step already produces a zero. Since the list is sorted, at most `Δ`
  vertices have degree at least two.

**Proof of the remaining case** (`k = 1`, `D` independent). Let `S` be a maximum 2-independent set
with `s = |S|`, and call a vertex small if its degree is at most `n - s`. A small vertex has degree
at least `s - 1` in `Ḡ`, so `s` small vertices give `WP(Ḡ) ≥ s`.

- If every vertex of `S` is small, we are done.
- Otherwise some `x ∈ S` has degree `n - s + 1`. So `x` is adjacent to all of `V - S` and to
  exactly one `y ∈ S`, and `N[y] ⊆ N[x]`.
  - Then `x ∈ D`. Since `D` is independent, `V - S` contains no neighbor dominators, and in
    particular no support vertices.
  - A vertex `v₁` of maximum degree has more neighbours than there are non-leaves, so it has a
    leaf. So `v₁ ∈ D ∩ S`, which forces `Δ = n - s + 1`. There are then at least `n - Δ = s - 1`
    leaves, all small.
  - If there are exactly `s - 1` leaves and no non-leaf is small, every non-leaf has degree
    `Δ = |H|`, where `H` is the set of non-leaves. So every non-leaf has a leaf neighbour, and
    every non-leaf lies in `D`.
  - Some neighbour of `v₁` is a non-leaf. Otherwise `v₁` and its leaves would be all of `G`,
    contradicting `|H| ≥ 2`. That neighbour and `v₁` are adjacent vertices of `D`, which is a
    contradiction.

An exhaustive check up to 9 vertices, annealing up to 20 vertices and a structured search
(`experiments/s436.cpp`) found no graph with `k = 1`, independent `D` and `α_2 > WP(Ḡ)`, as the
proof predicts.

**Formalization.** `WOWII436c.conjecture436c` in `OpenProblem/WOWII436c.lean` depends only on the
standard axioms. It defines the Havel–Hakimi process explicitly. The key case is
`WOWII436c.twoIndepNum_le_WP`.

## WOWII 319: false

> Let `G` be a simple connected graph with `n > 1`. If `max_v dist_even(v) = γ(G)`, then `G` is
> well totally dominated.

Here `dist_even(v)` counts the vertices at even distance from `v`, including `v` itself (as in
formal-conjectures' `SimpleGraph.distEven`). WOWII lists this conjecture as open, and it has no
activity on the formal-conjectures tracker (checked October 21, 2026).

The vertices at even distance from any `v` form a dominating set, so `γ ≤ min_v dist_even(v)`.
The hypothesis therefore forces every `dist_even(v)` to equal `γ`. An exhaustive search
(`experiments/h319.c`) lists all connected graphs on at most 10 vertices that satisfy it. Apart
from one graph, they are:

- the complete graphs;
- the cocktail party graphs `K_{2,…,2}`;
- the coronas `H ∘ K₁`;
- `C_7`.

All of these are well totally dominated.

**Counterexample.** The exception is the graph `I?`D@`WH_`, with 10 vertices, 12 edges and degrees
`2, 2, 2, 2, 2, 2, 3, 3, 3, 3`. Its edges are 0-4, 0-6, 1-5, 1-8, 2-6, 2-7, 2-9, 3-7, 3-8, 4-8,
5-9 and 6-9.

- Every vertex has exactly four vertices at even distance (itself and three at distance 2).
- `γ = 4`: `{0, 1, 2, 3}` dominates, and no three vertices do.
- `{1, 2, 6, 8}` and `{0, 1, 3, 6, 8}` are minimal total dominating sets. There are also minimal
  ones of size 6.

So the hypothesis holds but `G` is not well totally dominated. By the search above, no smaller
counterexample exists.

**Formalization.** `WOWII319.not_conjecture319` in `OpenProblem/WOWII319.lean` depends only on
the standard axioms. The distances are certified by breadth-first search tables
(`dist_eq_of_bfs`), and the finite checks use `decide`.

## WOWII 321: proved

> Let `G` be a simple connected graph with `n > 1`. If `ecc_avg(G) ≥ (1/3) Tdist_max(G)`, then `G`
> is well totally dominated.

Here `Tdist(v) = Σ_u d(v, u)`. WOWII lists this conjecture as open, and it has no activity on the
formal-conjectures tracker (checked October 21, 2026). In integers the hypothesis reads
`n · Tdist(w) ≤ 3 Σ_v ecc(v)` for every `w`.

**Proof.**

- **At most six vertices.** Let `x, y` realise the diameter `D`. Summing `d(x, v) + d(v, y) ≥ D`
  over all `v` gives `Tdist(x) + Tdist(y) ≥ nD`. Since every eccentricity is at most `D`, the
  hypothesis gives `Tdist(x), Tdist(y) ≤ 3D`. Hence `n ≤ 6`.
- **Six vertices.** All of these inequalities are now tight:
  - every vertex `x` has eccentricity `D`;
  - every vertex has an antipode `y` with `Tdist(x) = 3D`;
  - every vertex lies on a shortest path from `x` to `y`.

  So the four vertices other than `x` and `y` have distances from `x` in `[1, D - 1]` that sum to
  `2D`.
  - `D = 1` is impossible.
  - `D = 2`: every vertex has exactly one non-neighbour (`K_{2,2,2}`). Every edge is then a total
    dominating set, so every minimal one has size 2.
  - `D = 3`: the distances are two 1s and two 2s, so the graph is 2-regular (`C_6`). For a minimal
    total dominating set `S`, let `f(v)` be the number of neighbours of `v` in `S`. Then
    `Σ f = 2|S|` and `1 ≤ f ≤ 2`.
    - Each vertex of `S` has a private neighbour, which gives `|S|` vertices with `f = 1`. Hence
      `2|S| ≤ 12 - |S|`, so `|S| ≤ 4`.
    - Also `2|S| ≥ 6`, so `|S| ≥ 3`.
    - If `|S| = 3`, every vertex has `f = 1`, so `S` would induce a perfect matching on three
      vertices, which is impossible. So `|S| = 4`.
  - `D ≥ 4` is impossible. A connected graph on 6 vertices has at least 5 edges, so some vertex
    `x` has two neighbours `p, q`. On a shortest path from `x` to its antipode, take the vertices
    `r, s` at distances `D - 1` and `D - 2`. Then `p, q, r, s` are the four other vertices, and
    their distances from `x` sum to `2D - 1 ≠ 2D`.
- **Two to five vertices.** Here the kernel checks every graph on two to five labelled vertices
  (1, 8, 64 and 1024 graphs) by `decide +kernel`, using a checker that:
  - computes distances by breadth-first search on bit masks;
  - enumerates all vertex sets to compare the sizes of the minimal total dominating sets.

  The checker's correctness is proved in Lean: the BFS masks against `SimpleGraph.dist`, and the
  masks against `Finset`s. So the result needs no trusted computation. The kernel check takes about
  20 seconds.

The 16 graphs satisfying the hypothesis are `K_2`, `P_3`, `K_3`, `K_{1,3}`, `P_4`, the paw, `C_4`,
`K_4 - e`, `K_4`, `K_{2,3}`, `C_5`, the house, `K_{2,3}` plus an edge, `K_{1,2,2}`, `C_6` and
`K_{2,2,2}` (`experiments/c321.py`).

**Formalization.** `WOWII321.conjecture321` in `OpenProblem/WOWII321.lean` depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## WOWII 323: proved

> Let `G` be a simple connected graph with `n > 1`. If
> `max {|N_Ḡ(e)| : e ∈ E(Ḡ)} ≤ 1 + max {dist_odd(v) - odd horizontal(v)}`, then `G` is well totally
> dominated.

`N_Ḡ(uw) = N_Ḡ(u) ∪ N_Ḡ(w)`. `odd horizontal(v)` counts the edges whose endpoints are at the same
odd distance from `v`, as in formal-conjectures' 309. WOWII lists this conjecture as open, and it
has no activity on the formal-conjectures tracker (checked October 2026). Among connected graphs
with at most 9 vertices, the hypothesis holds only for complete bipartite graphs with a few edges
added inside the parts (`experiments/h323.py`). That suggested the proof.

**Proof.** Let `v` attain the maximum, let `L` be the left-hand side, and set `A = N(v)` and
`B = V - A`.

1. *Diameter at most two.* If `d(x, y) ≥ 3`, then `x` and `y` have disjoint closed
   neighbourhoods, so `|N_Ḡ(x) ∪ N_Ḡ(y)| = n`. Hence `dist_odd(v) ≥ n - 1`, and every other
   vertex is at odd distance from `v`. A vertex at distance at least 3 would give one at distance
   2, so all vertices are adjacent to `v`, contradicting `d(x, y) ≥ 3`.
2. *Rewriting the hypothesis.* Now `dist_odd(v) ≤ deg v`, and `odd horizontal(v) ≥ |E(G[A])|`. For
   non-adjacent `u ≠ w`, `|N_Ḡ(u) ∪ N_Ḡ(w)| = n - |N(u) ∩ N(w)|`. So every non-adjacent pair has at
   least `n - L` common neighbours, and `|E(G[A])| ≤ 1 + |A| - L`.
3. *`G` contains all edges between `A` and `B`.* Suppose `b ∈ B - {v}` is not adjacent to
   `a ∈ A`. Their common neighbours lie in `N_A(a) ∪ (B - {b, v})`. That gives at most
   `|E(G[A])| + |B| - 2 ≤ n - L - 1` of them, which is a contradiction.
4. *Every minimal total dominating set has two vertices.*
   - A set containing `a ∈ A` and `b ∈ B` contains the dominating pair `{a, b}`.
   - A set inside `B` cannot dominate `v`.
   - A minimal set inside `A` contains an edge `xy`. Suppose `z ∈ A` missed both `x` and `y`. Let
     `K` be the common `A`-neighbours of `z` and `x`. Then step 2 gives `|K| ≥ |E(G[A])| - 1`.
   - The edges `xy`, `zw` and `xw` for `w ∈ K` give `|E(G[A])| ≥ 1 + 2|K|`, so `G[A]` has at most
     one edge. But `z`'s neighbour in the set gives a second edge, which is a contradiction. So
     `{x, y}` dominates.

**Formalization.** `WOWII323.conjecture323` in `OpenProblem/WOWII323.lean` depends only on the
standard axioms.

## WOWII 325: proved

> Let `G` be a simple connected graph with `n > 1`. If
> `min {|N_Ḡ(e)| : e ∈ E(Ḡ)} ≤ 1 + c`, where `c` is the number of components of `⟨N[S]⟩` and `S` is
> the set of degree-two vertices, then `G` is well totally dominated.

WOWII lists this conjecture as open, and it has no activity on the formal-conjectures tracker
(checked October 2026). Among connected graphs up to 9 vertices, every graph satisfying the
hypothesis has two non-adjacent vertices `u`, `w` that are adjacent to all other vertices, and has
`c = 1` (`experiments/hW3.py`).

**Proof.** Let `uw` be an edge of `Ḡ` attaining the minimum, `X = N(u) ∩ N(w)` and
`R = V - X - {u, w}`. Since `|N_Ḡ(u) ∪ N_Ḡ(w)| = n - |X|`, the hypothesis is `|R| + 1 ≤ c`. Each
component of `⟨N[S]⟩` contains a degree-two vertex and its two neighbours, so it has at least three
vertices. So `3c ≤ |N[S]|`, and also `c ≤ |S|`.

- *A degree-two vertex `s` lies in `X`.* Then `N(s) = {u, w}`. So `u`, `w` and `X ∩ N[S]` all lie in
  one component, and the other components lie inside `R`. Hence `3(c - 1) ≤ |R| ≤ c - 1`, so `c = 1`
  and `R = ∅`.
- *No degree-two vertex lies in `X`.*
  - If neither `u` nor `w` has degree two, then `S ⊆ R` and `c ≤ |S| ≤ |R|`, which contradicts the
    hypothesis.
  - Otherwise `|X| ≤ 2`, and `3c ≤ n = |R| + |X| + 2` forces `c ≤ 1`, `R = ∅` and `n ≤ 4`.

In both cases `u` and `w` are adjacent to everything else.

- A minimal total dominating set containing `u` (or `w`) contains a neighbour `x ∈ X`, and `{u, x}`
  already dominates. So it is that pair.
- A total dominating set inside `X` would have to dominate the degree-two vertex `s` of the first
  case, whose neighbours are `u` and `w`. In the second case `|X| ≤ 2`, so such a set is a pair.

**Formalization.** `WOWII325.conjecture325` in `OpenProblem/WOWII325.lean` depends only on the
standard axioms. It counts the components of the induced subgraph through the connected components
of `G.induce`. `WOWII325.conjecture325'` adds complete graphs, where `Ḡ` has no edges.

## WOWII 169: proved

> If `G` is a simple connected graph, then
> `L_s(G) ≥ 1 + maximum of dist_even(v) − minimum of dist_even(v)`.

WOWII lists this conjecture as open.

**Proof.**

- **A tree whose edges cross parity.** Fix a root `r`. The edges whose ends lie at different
  distances from `r` form a connected spanning subgraph, because each vertex has a neighbour one
  step closer to `r`. A spanning tree `T` of this subgraph has every edge joining an even-distance
  vertex to an odd-distance one.
- **A degree count.** If every edge of a tree has exactly one end in `X`, then
  `∑_{x∈X} deg x = n − 1`. Each vertex has degree at least 1, and at least 2 unless it is a leaf,
  so `2|X| ≤ n − 1 + #leaves(X)`.
- **Combining.** Root at the `dist_even` minimiser and take `X` = the odd vertices: this gives
  `n − 2·min ≤ L_s − 1`. Root at the maximiser and take `X` = the even vertices: this gives
  `2·max − n ≤ L_s − 1`. Adding the two proves the conjecture.

**Formalization.** `WOWII169.conjecture169` in `OpenProblem/WOWII169.lean` depends only on the
standard axioms.

## WOWII 96: proved

> If `G` is a simple connected graph, then
> `α(G) ≤ 1 + minimum dist_even(v) · (maximum of λ(v) − 1)`.

Here `dist_even(v)` counts the vertices at even distance from `v` (including `v`), and
`λ(v) = α(G[N(v)])`. WOWII lists this conjecture as open (dated April 2004).

We prove the stronger statement that `α(G) ≤ 1 + dist_even(v)(λ_max − 1)` for **every** vertex
`v`.

**Proof.** Fix `v`, a maximum independent set `I`, and the BFS layers from `v`. Each vertex of `I`
in an odd layer has a neighbour in the previous layer, which is even; map it there. Let `w` be an
even vertex.

- If `w ∈ I`, nothing maps to `w`.
- If `w ∉ I` and `w ≠ v`, the vertices mapped to `w` lie two layers below `w`'s own neighbour `q`
  in the previous layer, so they are not adjacent to `q`. Together with `q` they form an
  independent subset of `N(w)`, so at most `λ(w) − 1` vertices map to `w`.
- The root `v` receives at most `λ(v)`.

Summing over the even vertices gives `|I| ≤ λ_max + (dist_even(v) − 1)(λ_max − 1)`. If
`λ_max = 1`, then `G` is complete. Equality holds for stars, using `v` = the centre.

**Formalization.** `OpenProblem/WOWII96.lean` contains `WOWII96.indepNum_le` (the every-vertex
form) and `conjecture96`. Both depend only on the standard axioms.

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

**WOWII 320 is also proved** (`OpenProblem/WOWII320.lean`).

> If `maximum dist_even(v) = Tdist_min(G)`, then `G` is well totally dominated.

The two sides are bounded on either side of `n − 1`:

- `Tdist(w) ≥ 2(n−1) − deg(w) ≥ n − 1`.
- `dist_even(v) ≤ n − deg(v) ≤ n − 1`.

So equality forces a universal vertex and a leaf. The leaf's neighbour is universal and lies in
every total dominating set, so every minimal total dominating set has exactly two vertices.

**WOWII 318 is also proved** (`OpenProblem/WOWII318.lean`).

> If `maximum dist_even(v) ≥ |E(Ḡ)|`, then `G` is well totally dominated.

Since `dist_even(v) ≤ 1 + deg_Ḡ(v)`, the hypothesis gives a vertex `x` such that all
non-adjacent pairs except at most one contain `x`. A minimal total dominating set `S` contains a
neighbour `z` of `x`.

- If `z` is universal, then `z` with any neighbour of `z` in `S` is a total dominating set.
- Otherwise `z` has a single non-neighbour `b`, and `z` with a neighbour of `b` in `S` is a total
  dominating set.

So every minimal total dominating set has two vertices. Connectivity is not needed.

The related conjectures 319, 321, 324, 325 and 328 also hold for all connected graphs up to 9
vertices. Since then, 319 has been refuted on 10 vertices, and 321 and 325 have been proved; see
their own sections.

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

## WOWII 361: proved

> If `T` is a tree on `n > 2` vertices, then `γ_t(T) ≥ number of isolates of <S(T)> + |C|`, where
> `S(T)` is the set of support vertices of `T` and `C` is the center of `T`.

Let `D` be a minimum total dominating set. A leaf is dominated only by its neighbour, so `D`
contains `S = S(T)`. A tree has at most two centers, and two centers are adjacent.

- If two support vertices are adjacent, neither is an isolate of `<S>`. Then
  `|D| ≥ |S| ≥ #isolates + 2 ≥ #isolates + |C|`.
- Otherwise `S` is independent and every vertex of `S` is an isolate. Each support vertex needs a
  neighbour in `D - S`, so `|D| ≥ |S| + 1`. It remains to rule out `D = S ∪ {t}` when `T` has two
  centers.
  - Every support vertex is adjacent to `t`, and every vertex is adjacent to `t` or to a support
    vertex. So `ecc(t) ≤ 2`.
  - Two adjacent centers of eccentricity at most 1 would form a triangle with any third vertex.
    So the radius is 2, and `t` is a center.
  - A neighbour of `t` outside `S` has a second neighbour, which closes a triangle or a 4-cycle.
    So every neighbour of `t` lies in `S`, including the other center `c`.
  - If `t` had a second neighbour `u`, the leaf at `u` would be at distance 3 from `c`. So `t` is
    a leaf at `c`, and then every vertex is within distance 1 of `c`, a contradiction.

The bound is tight, for example on stars and on spiders with legs of length 2. All trees up to
18 vertices were checked first (`experiments/t361.cpp`, which also checks 376).

Tracker: PR google-deepmind/formal-conjectures#7377 (October 15, 2026) adds the statement with
`sorry`, including a variant for `n > 1`. It cites an undated manuscript, "A Support–Center Lower
Bound for Total Domination in Trees", whose argument we have not seen. So 361 may already have an
informal proof, and what we add is a complete Lean proof found independently. Our theorem also
covers the `n > 1` variant.

**Formalization.** `WOWII361.conjecture361` in `OpenProblem/WOWII361.lean` covers all trees with
at least two vertices. It depends only on the standard axioms.

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

### Examined but not resolved (October 2026, second pass)

These conjectures have no tracker activity. Each was tested with exact branch-and-bound
invariants (`experiments/sa11.cpp` to `sa16.cpp`) and left open for the reason given.

- **Holds in every test, no proof found:**
  - 61 (`f ≥ res + ⌈diam/3⌉`): annealing up to 24 vertices, with growing slack (`sa61.cpp`).
  - 448a, with `ρ` the path cover number: tight up to 14 vertices.
  - 450, with `p N(X)` the path cover number of `G[N(X)]`: up to 14 vertices.
  - The bipartite part of 412f (`|H| ≥ c(G[V - N(P)]) + μ(G[V - N(P)])`, with `H` the union of
    maximum critical independent sets): all bipartite graphs up to 10 vertices, and bipartite
    annealing up to 18. It is tight throughout.
  - 434d and 434e: these follow from `i ≤ SW(Ḡ)` unless the component count or `ecc(C)` exceeds
    `2`. A path argument handles `ecc(C) ≤ 4`, but not beyond.
  - The Hamiltonian-path conditions 189, 190, 199 and 213, and 177, 384b and 418b, up to
    15 vertices (`sa14.cpp`).
- **Fails on tiny graphs under the natural reading (likely transcription problems):**
  - the general part of 412f, which fails on `K_3` and `K_4` because their only critical
    independent set is empty (now formalized; see "WOWII 412f: false as stated");
  - 398, which fails on 5 vertices;
  - 446, and 448a with `ρ` the longest induced path, which fail on 6 vertices;
  - 448b under both readings of `ρ`.
- **Undefined or ambiguous invariants:**
  - 66 (`even_mode_min`), 154 and 155 ("radial circles"), 157 (`f_1`, `R(v)`) and 171;
  - 341 (`σ(T)`) and 369;
  - 382e (Maxine) and 389a (quartile convention). (391 is now shown false as stated.)
  - 400c and 401a (disparity), 413a and 413b (`c_L`), 415a–c (`epN`), and 431a and 431b
    (`peN`);
  - 432a and 432b, and 443 (disparities). (427 is now refuted under both readings of `C`.)

### Exhaustive search on 10 vertices (October 2026)

`experiments/n10.cpp` and `experiments/n10b.cpp` check the following on all 11,716,571 connected
graphs with 10 vertices:

- `γ_t` bounds: 232, 233, 235, 255, 256, 268, 269, 287, 290, 299, 302 and 304;
- `i` bounds: 418b, 421b, 421c, 422a, 422c, 431c, 434d and 434e (and the stronger
  `i ≤ n - Δ - ecc(C) + 2`);
- `γ_2` bounds: 382c, 382d, 387, 392b–f, 395a and 399c;
- `α_2`: 448a, with `ρ` the path cover number;
- well total domination: 324;
- Hamiltonian paths: 189, 190, 199 and 213.

None fails, except 269 under the reading "mean distance from the centre to all vertices", which
already fails on `P_4`. Many are tight. Two of them, 255 and 256, were refuted afterwards by
constructions on 11 and 15 vertices; see their sections.

For 324, all hypothesis graphs up to 10 vertices fall into a few dense families. These are `K_n`,
the cocktail party graphs, the complements of disjoint unions of `K_2`, `P_3` and `K_3`, and the
complete split graphs, plus a few graphs with residue `R = Δ(Ḡ) ≥ 3`. In all of them every minimal
total dominating set has two vertices.

The hypothesis forces `Δ(Ḡ) ≤ R`, and the Favaron–Mahéo–Saclé bound `R ≤ α(G) = ω(Ḡ)` gives
`Δ(Ḡ) ≤ R ≤ ω(Ḡ)`. When `R = 2`, `Ḡ` is a disjoint union of `K_2`, `P_3` and `K_3`, and `G` is
well totally dominated: any two vertices from different factors of the join form a total
dominating set. A full proof would need finer upper bounds on the Havel–Hakimi residue, since with
`α` in place of `R` the statement fails on 7 vertices.

### Exhaustive search on 11 vertices (October 2026)

`experiments/n10c.cpp` checks the lower bounds 72 (both readings), 76, 84, 165, 166 and 258–261
on all 1,006,700,565 connected graphs with 11 vertices (16 shards of `geng -c 11`). None fails.
The minimum slack is `0` for 72a, 84, 165, 166 and 258–260, `2/3` for 261 and `1` for 72b and 76.

`wowii/experiments/c40.cpp` checks 40 (`f ≥ ⌈(p + b + 1)/2⌉`) and 100 on all 11,716,571 connected
graphs with 10 vertices. Neither fails, and both are tight. Up to 8 vertices every equality case
of 40 has `p = 1`. The case `p ≤ 1` is easy: the larger side `X` of a maximum induced bipartite
subgraph, plus one neighbour, is an induced forest, so `2f ≥ b + 2`. For 100, a proof appears on
the tracker (formal-conjectures PR #5221).

### Dead ends recorded (October 22, 2026)

- 199: the route through Chvátal–Erdős fails. The lemma "`α ≥ κ + 2` implies `tree ≥ κ + 3`" is
  false on 7 vertices (`F?z\w`), although that graph has a Hamiltonian path
  (`experiments/c199.cpp`).
- 61: the stronger `f ≥ α + ⌈diam/3⌉` fails on 6 vertices (`E?zO`), so a proof must use
  `res < α`.
- 72: under the reading `tree ≥ ⌈(ecc_avg + λ_max)/3⌉` the bound is trivial, since
  `tree ≥ max(diam, λ_max) + 1`. Under the reading `tree ≥ ⌈ecc_avg + λ_max/3⌉`:
  - The equality cases up to 9 vertices are two hubs sharing several common neighbours, with
    pendant paths at the hubs (`experiments/eq72.cpp`).
  - Annealing at 14–22 vertices found slack of at least 1 (`experiments/s72.cpp`).

### TxGraffiti Conjecture 3 (refuted by others)

*Update (October 2026):* formal-conjectures issue #6737 records a 48-vertex cubic counterexample
with `i = 16 > μ* = 15`, and an earlier 50-vertex one. This is consistent with the searches below,
which stop at 20 vertices for cubic graphs. We make no claim about this conjecture.


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

Since then, 161 and 179 have been proved, and 281 and 300 have been refuted by targeted
simulated annealing (counterexamples on 13 and 12 vertices) that random sampling had missed. For
84, 165, 166, 174, 177, 180, 183, 185, 255, 256, 268, 232, 233, 382c, 382d, 384b, 387, 392b–f,
299, 302 and 304, annealing found nothing (`experiments/saLb.cpp`, `experiments/sagt.cpp`).

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
- The total domination bounds 232, 233 and 235 (with `ecc(B)` read as `max_v d(v, B)` for `B` the
  periphery or the boundary), 268 and 269 (pairwise mean distance of the centre), 287, 290, 298,
  299, 302, 304 and 305 hold for all connected graphs up to 9 vertices
  (`experiments/t302.cpp`). For 298, `χ_C4` is the indicator of being C4-free, as in 133: with
  the opposite reading, the conjecture fails on `C3`, `C5`, `C6`, `C7` and `P6`.
- The Hamiltonian-path conditions 189, 190 and 213 hold for all connected graphs up to 9
  vertices. For 189 this uses `dist_even(v)` counting `v` itself; the other reading already fails
  on `K_{1,3}`.
