# Graffiti-type graph conjectures: notes

Status: **WOWII Conjecture 178 is proved and verified in Lean** (`OpenProblem/WOWII178.lean`).
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
None failed on any connected graph with at most 9 vertices, nor on about 143,000 random graphs
with 10–15 vertices.
