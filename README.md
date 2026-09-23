# Unit-distance graphs of dimension five with fifteen edges

A Lean 4 proof of the dimension-five case of the question behind Erdős problem 1007: a graph of
dimension five has at least fifteen edges, and both `K₆` and `K₁,₃,₃` have exactly fifteen.

> A graph has **dimension** `n` when `n` is the least number such that its vertices can be placed
> injectively in `ℝⁿ` with every edge a unit segment (Erdős, Harary and Tutte, 1965). Chaffee and
> Noble proved that a graph of dimension five has at least fifteen edges, and that `K₆` and
> `K₁,₃,₃` are the only graphs of dimension five with fifteen. This repository proves the bound and
> that both graphs attain it. It does not formalize their uniqueness.

| | |
|---|---|
| Proof | complete: no `sorry`; only `propext`, `Classical.choice` and `Quot.sound` |
| Comparator | accepted by Lean's kernel and by NanoDa ([record](docs/comparator-2026-09-23.md)) |
| Library | [GraphDimension](https://github.com/Dishah3241/GraphDimension), which Lake fetches at the revision pinned in `lake-manifest.json` |
| Review | an independent, read-only review found nothing that blocks the proof ([record](docs/review-2026-09-23.md)) |
| Blueprint | [web](https://dishah3241.github.io/Erdos1007Dim5/) and [PDF](https://dishah3241.github.io/Erdos1007Dim5/blueprint.pdf), built by CI from `blueprint/src/content.tex` and checked against the Lean by `leanblueprint checkdecls` |
| `formal-conjectures` link | not yet proposed |
| Palomar entry | not yet submitted |

## Context

Erdős asked for the least number of edges of a graph of dimension four. House answered nine, and
showed that only `K₃,₃` attains it; [Erdos1007](https://github.com/Dishah3241/Erdos1007) formalizes
that uniqueness. `formal-conjectures` also records the next case, dimension five, which Chaffee and
Noble settled. Write `f(d)` for the least number of edges of a graph with no unit-distance
representation in `ℝᵈ`. Since `K_{d+2}` has none, `f(d) ≤ C(d + 2, 2)`, and Frankl, Kupavskii and
Swanepoel proved equality for every `d ≥ 4`. At `d = 4` that is fifteen, the bound proved here,
which Chaffee and Noble proved first.

## The statements

They are `erdos_1007.variants.dimension_five` and `erdos_1007.variants.dimension_five_extremal`
from [google-deepmind/formal-conjectures][fc].
`Erdos1007Dim5/Standalone/Mathlib/InlineErdos1007Dim5.lean` restates them with their definitions
inlined, so that they depend on Mathlib alone:

```lean
def DimensionFive : Prop :=
  IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), HasDimension G 5 ∧ G.edgeSet.ncard = m} 15

def DimensionFiveExtremal : Prop :=
  (HasDimension (SimpleGraph.completeGraph (Fin 6)) 5 ∧
      (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
    (HasDimension K133 5 ∧ K133.edgeSet.ncard = 15)
```

`DimensionFive.proof` and `DimensionFiveExtremal.proof` in `InlineErdos1007Dim5Proof.lean` prove
them. `Solution.lean` states their conjunction as `Erdos1007Dim5.Palomar.target`, which Comparator
checks against `Challenge.lean`.

Why the statements mean the claim:

- **They are upstream's statements.** With both builds loaded together, each equals the type of
  upstream's declaration by `rfl` ([record](docs/upstream-check-stage1.md)). Both proofs also
  elaborate against upstream's declaration types in one environment
  ([record](docs/upstream-check-2026-09-23.md)).
- **Neither is vacuous.** Neither has a hypothesis. `DimensionFive.witness` asserts that some graph
  of dimension five has fifteen edges, and `DimensionFiveExtremal.witness` that `K₆` and `K₁,₃,₃`
  are different graphs. Both are proved.
- **Each definition means what it says.** [`docs/compass.md`](docs/compass.md) lists what every
  statement-level declaration must mean, and each definition has a separating example.

## The proof

It follows Chaffee and Noble's Theorems 8 and 10 and Lemma 9, from the paper below.

1. **Theorem 10.** Every finite graph with at most fourteen edges has a unit-distance
   representation in `ℝ⁴`, by induction on vertices. Delete a vertex of degree at most three and
   join its neighbours to one another. The smaller graph has no more edges, so it has a
   representation. The neighbours are now at most three points at pairwise distance one. In `ℝ⁴`
   the unit spheres about them share infinitely many points, so the vertex goes back on one of
   them, away from the finitely many points already used. If instead every degree is at least four,
   then `4|V| ≤ 2 · 14` gives at most seven vertices. On at most five vertices the graph lies inside
   `K₅`, and on six inside `K₆ − e`; both have dimension four. On seven it is four-regular, its
   two-regular complement has three disjoint edges, and so it maps into `K₁,₂,₂,₂`, which has
   dimension four (Lemma 9).
2. **`K₆` has dimension five.** At most `d + 1` points of `ℝᵈ` are pairwise at distance one, so
   `K₆` does not fit in `ℝ⁴`. The points `(1/√2) eᵢ` of `ℝ⁶` are pairwise at distance one and
   lie in a hyperplane, which carries them isometrically into `ℝ⁵`.
3. **Theorem 8: `K₁,₃,₃` has dimension five.** An explicit placement puts it in `ℝ⁵`. An
   orthogonal-complement count rules out `ℝ⁴`, in place of the paper's circumcentre argument.
4. **The statements.** `K₆` has dimension five and fifteen edges, and by step 1 no graph with
   fewer edges has dimension five, so fifteen is least. Steps 2 and 3 give attainment.

The general results are in the GraphDimension library, in its `SimpleGraph` namespace unless the
table says otherwise:

| Step | Declaration | Module |
|---|---|---|
| 1 | `unitDistEmbeddable_four_of_ncard_edgeSet_le` | `Extremal/FourteenEdges.lean` |
| 1, re-attaching | `UnitDistEmbeddable.extend`; `EuclideanGeometry.infinite_sphere_inter_of_regular_simplex` | `Geometry/Extend.lean`; `Geometry/SimplexSphere.lean` |
| 1, `K₆ − e` | `hasUnitDistDim_completeGraph_deleteEdge` | `Geometry/CompleteMinusEdgeDimension.lean` |
| 1, seven vertices | `exists_three_pairwise_disjoint_edges_compl` | `Combinatorics/SimpleGraph/TwoRegularSeven.lean` |
| 1, Lemma 9 | `hasUnitDistDim_completeMultipartiteGraph_one_two_two_two` | `Geometry/Cocktail.lean` |
| 2 | `hasUnitDistDim_completeGraph`, from `EuclideanGeometry.card_le_of_equilateral` | `Geometry/CompleteGraph.lean`; `Geometry/Equilateral.lean` |
| 3 | `hasUnitDistDim_K133` | `Geometry/K133.lean` |

Step 4 is `DimensionFive.proof` and `DimensionFiveExtremal.proof`, in namespace
`Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5`. The library's `UnitDistEmbeddable` and
`HasUnitDistDim` have the same bodies as the inlined definitions, and `unitDistanceEmbeddable_iff`
and `hasDimension_iff` connect them. The [blueprint](https://dishah3241.github.io/Erdos1007Dim5/)
lays out the same steps as a dependency graph.

## Checking it

With Lean `v4.33.1` and Mathlib `0df444a`, the same pins as `formal-conjectures`:

```sh
lake exe cache get
lake build
lake exe axioms && lake exe fidelity && lake exe proof-links && lake exe palomar-compatibility
lake exe module-system && lake exe standalone-mathlib && lake exe layering
lake exe style && lake exe documentation
scripts/lint-env.sh && scripts/check-palomar-challenge.sh && scripts/audit-probes.sh
leanblueprint checkdecls
```

`lake build` also fetches and builds GraphDimension at its pinned revision.
`scripts/audit-probes.sh` checks that each audit rejects the defect it exists to catch. The
Comparator command is in [`docs/comparator-2026-09-23.md`](docs/comparator-2026-09-23.md).

## Sources

- Joe Chaffee and Matt Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*,
  [Australas. J. Combin. **64(2)** (2016), 327–333][cn], Theorem 8, Lemma 9 and Theorem 10. The
  proof of record; it is open access.
- Paul Erdős, Frank Harary and William T. Tutte, *On the dimension of a graph*, Mathematika **12**
  (1965), 118–122, [doi:10.1112/S0025579300005222](https://doi.org/10.1112/S0025579300005222).
- Nóra Frankl, Andrey Kupavskii and Konrad J. Swanepoel, *Embedding graphs in Euclidean space*,
  J. Combin. Theory Ser. A **171** (2020), 105146,
  [doi:10.1016/j.jcta.2019.105146](https://doi.org/10.1016/j.jcta.2019.105146). Context: `f(d)` for
  every `d ≥ 4`.
- T. F. Bloom, Erdős Problem #1007, <https://www.erdosproblems.com/1007>.

## How this was made

AI agents wrote the Lean under the direction of its owner, who chose the problem and approved
publication. [`formalization.yaml`](formalization.yaml) names every model and harness, phase by
phase:

- **Statement:** GLM-5.3-flash through pi. Grok 4.7, through the Grok CLI, checked it against
  upstream.
- **Library and proof:** Grok 4.7, through the Grok CLI and through Cursor, and GLM-5.3-flash
  through pi.
- **Management and independent proof review:** Claude Opus 5.5.

No human has reviewed the proof itself. Its correctness rests on the kernel checks above.

## Licence

Apache-2.0. See [`LICENSE`](LICENSE).

[fc]: https://github.com/google-deepmind/formal-conjectures
[cn]: https://ajc.maths.uq.edu.au/pdf/64/ajc_v64_p327.pdf
