/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Erdős 1007, dimension five: fifteen edges, attained by K6 and K1,3,3

A graph has *dimension* `n` when `n` is least such that its vertices can be placed injectively in
`ℝⁿ` with every edge realised as a unit segment. Chaffee and Noble proved that a graph of
dimension five has at least fifteen edges, and that fifteen is attained by both `K₆` and `K₁,₃,₃`.
This file states both halves.

`Challenge.lean` is generated from this file; see `AGENTS.md`. Everything here rests on Mathlib
alone, so a reader can check the statement without following a definition elsewhere.

## Source

The statements are the `erdos_1007.variants.dimension_five` and
`erdos_1007.variants.dimension_five_extremal` declarations of
[google-deepmind/formal-conjectures][fc], reproduced with their definitions inlined and no change
of meaning, together with the source's `K133`. The proof of record is Chaffee and Noble,
*Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J. Combin. **64(2)** (2016),
327–333, Theorem 8, Lemma 9 and Theorem 10.

[fc]: https://github.com/google-deepmind/formal-conjectures
-/

@[expose] public section

namespace Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

open scoped RealInnerProductSpace

/-- The complete tripartite graph $K_{1,3,3}$.

Reproduced verbatim from the source statement, up to namespacing. The vertices are the dependent
sum of the three parts, of sizes one, three and three — seven vertices in all — and two vertices
are adjacent exactly when they lie in different parts. -/
abbrev K133 := SimpleGraph.completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)

/-- `G` admits a unit-distance representation in `ℝⁿ`: an injective placement of its vertices
sending every **edge** to a pair of points at distance one.

Non-adjacent vertices are unconstrained, so this is a unit-distance *representation* and not the
stricter notion of a unit-distance *graph*, where distance one would force adjacency. The source
claim asks only that every edge be a unit segment, so the weaker reading is the faithful one;
`UnitDistanceEmbeddable.separating` exhibits the difference. -/
def UnitDistanceEmbeddable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
    ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

/-- Separating example for `UnitDistanceEmbeddable`, required by `lake exe fidelity`.

The nearest plausible wrong definition adds `∀ u v, dist (f u) (f v) = 1 → G.Adj u v`, turning a
representation into a unit-distance graph. This exhibits a placement that satisfies the definition
as written while putting a **non-edge** at distance one, so the definition demonstrably does not
constrain non-adjacent vertices. Without it a development could silently prove the stricter
theorem, which is a different and stronger claim than the source makes.

An edge plus a third vertex in `ℝ¹` does it: send the edge to `0, 1` and the third vertex to `2`.
Every edge is a unit segment and the non-edge between the second and third vertices is also a unit
segment.

An earlier version of this asserted instead that **no** placement satisfies the stricter reading.
That was wrong, and an adversarial review kernel-checked the refutation: placing the third vertex
at `3` instead satisfies the stricter reading too. Non-existence of a strict placement is a much
stronger and harder claim, and it is not what separating the definitions requires. -/
def UnitDistanceEmbeddable.separating : Prop :=
  ∃ (V : Type) (G : SimpleGraph V) (n : ℕ) (f : V → EuclideanSpace ℝ (Fin n)),
    UnitDistanceEmbeddable G n ∧
      Function.Injective f ∧ (∀ u v : V, G.Adj u v → dist (f u) (f v) = 1) ∧
        ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v ∧ dist (f u) (f v) = 1

/-- `G` has dimension `n`: the least `m` admitting a unit-distance representation of `G` in `ℝᵐ`.

`IsLeast` carries both halves — `G` is representable in `ℝⁿ`, and in no smaller space. Weakening
this to mere representability in `ℝ⁵` would make the claims below false: the single edge `K₂` is
representable in `ℝ⁵`, so the least edge count would be one, not fifteen. -/
def HasDimension {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  IsLeast {m | UnitDistanceEmbeddable G m} n

/-- Separating example for `HasDimension`, required by `lake exe fidelity`.

The nearest plausible wrong definition is membership in place of leastness: `G` is representable
in `ℝⁿ`. This asserts a graph representable in `ℝ⁴` that does not have dimension four, separating
the two.

The edge is required because without it the empty graph satisfies this degenerately — it is
representable in every dimension and has dimension zero — which an adversarial review
kernel-checked. A separating example that only the empty object witnesses establishes nothing
about the definition, so this demands a graph with an edge. `K₂` is the intended witness:
representable in `ℝ⁴`, of dimension one. -/
def HasDimension.separating : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    (∃ u v : V, G.Adj u v) ∧ UnitDistanceEmbeddable G 4 ∧ ¬ HasDimension G 4

/-- Separating example for `K133`, required by `lake exe fidelity`.

The nearest plausible wrong reading of `K₁,₃,₃` is the complete graph on the same seven vertices:
Mathlib builds `completeMultipartiteGraph` as the complete graph pulled back along the part
index, and dropping the pullback leaves every pair of vertices adjacent. This asserts two distinct
`K₁,₃,₃` vertices that are not adjacent — take both from the second part — which the complete
graph on the same vertex set does not have. -/
def K133.separating : Prop :=
  ∃ u v : Σ i : Fin 3, Fin (![1, 3, 3] i), u ≠ v ∧ ¬ K133.Adj u v

/-- **Erdős problem 1007, dimension five.** The least number of edges of a graph of dimension
five is fifteen.

`IsLeast` carries both halves: some graph of dimension five has fifteen edges, and no graph with
fewer edges has dimension five. `DimensionFive.witness` asserts the first half separately, and
`DimensionFiveExtremal` names the two graphs that attain it. -/
def DimensionFive : Prop :=
  IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), HasDimension G 5 ∧ G.edgeSet.ncard = m} 15

/-- Satisfiability witness for `DimensionFive`, required by `lake exe fidelity`.

The claim is closed, so vacuity cannot come from unsatisfiable hypotheses; it would come from the
set being empty at fifteen. This asserts that fifteen belongs to the set — some graph of dimension
five with exactly fifteen edges exists. Discharging it is the attainment half of Chaffee and
Noble's result: `K₆` and `K₁,₃,₃` are such graphs. -/
def DimensionFive.witness : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), HasDimension G 5 ∧ G.edgeSet.ncard = 15

/-- **Erdős problem 1007, extremal half for dimension five.** Fifteen edges are attained by both
`K₆` and `K₁,₃,₃`: each has dimension five and exactly fifteen edges. -/
def DimensionFiveExtremal : Prop :=
  (HasDimension (SimpleGraph.completeGraph (Fin 6)) 5 ∧
      (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
    (HasDimension K133 5 ∧ K133.edgeSet.ncard = 15)

/-- Satisfiability witness for `DimensionFiveExtremal`, required by `lake exe fidelity`.

The claim is a conjunction about two named graphs, and it would be degenerate if the two names
denoted the same object: attainment by `K₆` and `K₁,₃,₃` would then mention one graph twice. This
asserts that the two graphs are not even isomorphic — six vertices against seven — so the
conjunction records attainment by two genuinely distinct graphs. -/
def DimensionFiveExtremal.witness : Prop :=
  ¬ Nonempty (SimpleGraph.completeGraph (Fin 6) ≃g K133)

end Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

/-!
## Formal proof

Proved in `InlineErdos1007Dim5Proof`.

* `separating` → `separating.proof`
* `DimensionFive` → `DimensionFive.proof`
* `DimensionFiveExtremal` → `DimensionFiveExtremal.proof`
* `witness` → `witness.proof`
-/
