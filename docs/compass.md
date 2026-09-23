# Compass list

The declarations whose meaning decides whether the two statements say what they claim. This is
the owner's whole review surface. Everything else, including the whole proof interior and the
GraphDimension library, is checked by the kernel and the gates.

The project declarations are in `Erdos1007Dim5/Standalone/Mathlib/InlineErdos1007Dim5.lean`,
namespace `Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5`. Rows 11 and 12 are Mathlib's.

**Owner sign-off: not yet given.** The owner signs by confirming every row. Any change to a row
cancels the sign-off.

- Rows 1, 2, 8 and 9 are the same upstream definitions and separating examples that the owner
  signed for Erdos1007 on 2026-09-22 (its `docs/compass.md`, rows 1, 2, 5 and 6).
- The proof reaches these statements through the library's copies of rows 1 and 2, whose bodies
  are the same. The kernel identifies them (`unitDistanceEmbeddable_iff` and `hasDimension_iff`),
  so that bridge needs no row.

| # | Declaration | Must mean | Check |
|---|---|---|---|
| 1 | `UnitDistanceEmbeddable G n` | an injective placement of the vertices in `ℝⁿ` with every edge at distance one | Non-edges are unconstrained. That is the source's reading, not the stricter unit-distance *graph*. |
| 2 | `HasDimension G n` | `n` is the **least** such dimension | `IsLeast`, not mere membership. Membership would make `DimensionFive` false: the single edge `K₂` fits in `ℝ⁵`, so the least edge count would be one. |
| 3 | `K133` | `K₁,₃,₃`: seven vertices in parts of sizes one, three and three, two vertices adjacent exactly when their parts differ | `![1, 3, 3]` gives the part sizes by index. It has `1·3 + 1·3 + 3·3 = 15` edges. |
| 4 | `DimensionFive` | fifteen is the least number of edges of a graph of dimension five | `IsLeast` over graphs on `Fin n` for every `n`: some graph of dimension five has fifteen edges, and none has fewer. |
| 5 | `DimensionFiveExtremal` | `K₆` and `K₁,₃,₃` each have dimension five and exactly fifteen edges | Attainment by both, not uniqueness. That they are the only such graphs (Chaffee–Noble Theorem 11) is out of scope. |
| 6 | `DimensionFive.witness` | some graph of dimension five has exactly fifteen edges | Guards against vacuity: the set in row 4 is not empty at fifteen. |
| 7 | `DimensionFiveExtremal.witness` | `K₆` and `K₁,₃,₃` are not isomorphic | Guards against the two names denoting one graph: six vertices against seven. |
| 8 | `UnitDistanceEmbeddable.separating` | some valid placement puts a **non-edge** at distance one | It asks for one looser placement, not for the absence of any strict placement. |
| 9 | `HasDimension.separating` | some graph **with an edge** is representable in `ℝ⁴` without having dimension four | Requiring an edge rules out the empty graph, which would satisfy it degenerately. |
| 10 | `K133.separating` | two distinct vertices of `K₁,₃,₃` are not adjacent | Separates it from the complete graph on the same seven vertices, the nearest misreading of `completeMultipartiteGraph`. |
| 11 | Mathlib `SimpleGraph.completeGraph (Fin 6)` | `K₆` | Every two distinct vertices of `Fin 6` are adjacent. |
| 12 | Mathlib `G.edgeSet.ncard = 15` | exactly fifteen edges | `ncard` is `0` on an infinite set, but every graph here is finite, so this is the true count. |
