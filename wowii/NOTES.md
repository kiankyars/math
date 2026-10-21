# Graffiti-type graph conjectures: notes

Status: **WOWII Conjectures 178, 348, 372 and 377 are proved and verified in Lean**
(`OpenProblem/WOWII178.lean`, `OpenProblem/WOWII348.lean`, `OpenProblem/WOWII372.lean`,
`OpenProblem/WOWII377.lean`).
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

WOWII 367 (`γ_t ≥ (4/3)·dd(T)` for trees whose most frequent degree is 2, where `dd` is the number
of distinct degrees) also holds for all trees up to 23 vertices when "most frequent" means a strict
mode. With ties allowed, it fails at 12 vertices, for example on the graph6 tree `K????B?KCWKW`.

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

- WOWII 174 (`L_s + b ≥ n + max λ - 1`, Conjecture 3 of DeLaViña–Waller 2008) and
  WOWII 177 (`L_s + b ≥ 2α + σ`, where `σ` is the second-smallest degree) hold for all connected
  graphs up to 9 vertices. Both have many equality cases, such as `C5` with pendants at one
  vertex. A targeted search of 20,000 spiders with mixed-parity legs plus vertices closing
  5-cycles found no counterexample to 174.
- The Hamiltonian-path conditions 189, 190 and 213 hold for all connected graphs up to 9
  vertices. For 189 this uses `dist_even(v)` counting `v` itself; the other reading already fails
  on `K_{1,3}`.
