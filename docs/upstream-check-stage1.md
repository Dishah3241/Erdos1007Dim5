# Upstream type check, Stage 1, 2026-09-22

This record shows that the inlined dimension-five statements are the same propositions as
`formal-conjectures`' own declarations. It is the inherited-path Stage 1 check from
`docs/PLAYBOOK.md`: `rfl` against upstream, rather than a second statement authored from the
paper. Skipping that second statement is the deliberate trade the playbook names, recorded
here. There is no proof module yet, so this check identifies the propositions and does not
inhabit them.

The inlining is commit `458466e8d4b316509a0ac68e2de99fc0296191cd`. This check was run as
factory run `20260922-221924-4ec70708`. `harness/run-model` reports that run's model as
not evidenced (the log has no final result event).

## Pins

- **`formal-conjectures` statement pin** `2a46c7bd74505b85f4967475bb733ded0ef8d348`, the commit
  named in `formalization.yaml`.
- **Fork whose compiled modules were loaded:** `~/src/formal-conjectures-fork` at
  `1bd90e66f970aa278ac3776754736aa5ca82f2a0` (`erdos1007-dimension-four-extremal-link`). Read
  only. It was not built, edited, fetched, or checked out. `git status` there was clean
  after the check.
- **This repository** at `458466e8d4b316509a0ac68e2de99fc0296191cd`, built with `lake build`.
- Both pin Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

### The fork against the pin

`1007.olean` in the fork is newer than `FormalConjectures/ErdosProblems/1007.lean`
(source 21:01:17, olean 21:01:38, both on 2026-09-22), so the loaded module is the working
tree. That working tree matches `HEAD`. Against the pin, the only change in the file is the
`formal_proof` attribute on `dimension_four_extremal`:

```text
git -C ~/src/formal-conjectures-fork diff 2a46c7bd74505b85f4967475bb733ded0ef8d348 -- FormalConjectures/ErdosProblems/1007.lean
```

```diff
@@ -58,7 +58,9 @@ theorem erdos_1007 :
 /--
 The smallest number of edges in a graph of dimension $4$ is achieved solely by $K_{3,3}$.
 -/
-@[category research solved, AMS 5 52]
+@[category research solved, AMS 5 52,
+  formal_proof using lean4 at
+    "https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Standalone/Mathlib/InlineErdos1007Proof.lean#L306"]
 theorem erdos_1007.variants.dimension_four_extremal (n : ℕ) (G : SimpleGraph (Fin n))
```

`K133`, `erdos_1007.variants.dimension_five`, and `erdos_1007.variants.dimension_five_extremal`
are byte-identical to the pin, including their docstrings and attributes. An attribute on the
dimension-four theorem does not change the types loaded for the two dimension-five theorems.

## The check

`tmp/Check.lean` (gitignored, as `tmp/` is):

```lean
import FormalConjectures.ErdosProblems.«1007»
import Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

/-!
Upstream `rfl` check: the inlined dimension-five statements are the same propositions as
`formal-conjectures`' declarations.
-/

/-- The inlined dimension-five statement and upstream's declaration type are the same proposition. -/
example : Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5.DimensionFive =
    type_of% @Erdos1007.erdos_1007.variants.dimension_five := rfl

/-- The inlined extremal statement and upstream's declaration type are the same proposition. -/
example : Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5.DimensionFiveExtremal =
    type_of% @Erdos1007.erdos_1007.variants.dimension_five_extremal := rfl

#check @Erdos1007.erdos_1007.variants.dimension_five
#check @Erdos1007.erdos_1007.variants.dimension_five_extremal
```

Upstream opens `namespace Erdos1007`, so the full names are
`Erdos1007.erdos_1007.variants.dimension_five` and
`Erdos1007.erdos_1007.variants.dimension_five_extremal`, and its `K133` is `Erdos1007.K133`.
This repository's declarations live under
`Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5`.

## Command

Run from the fork, with this worktree's compiled library appended to `LEAN_PATH`. The fork's
Mathlib and `FormalConjectures` come from `lake env`; this repository is not a dependency of
the fork.

```sh
cd ~/src/formal-conjectures-fork && ~/.elan/bin/lake env sh -c 'LEAN_PATH="$LEAN_PATH:$E/.lake/build/lib/lean" lean $E/tmp/Check.lean'   # E: this repository's checkout
```

## Result

Exit code 0. Full output:

```text
Erdos1007.erdos_1007.variants.dimension_five : IsLeast {m | ∃ n G, G.HasDimension 5 ∧ G.edgeSet.ncard = m} 15
Erdos1007.erdos_1007.variants.dimension_five_extremal : ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
    (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
  Erdos1007.K133.HasDimension 5 ∧ Erdos1007.K133.edgeSet.ncard = 15
```

Both `example`s elaborate by `rfl`, so each inlined `Prop` is definitionally the type of the
upstream theorem. The pretty-printer drops the binders inside `∃ n G`; the source on both
sides is `∃ (n : ℕ) (G : SimpleGraph (Fin n))`, and `rfl` is equality of those elaborated
terms. `∧` is right-associative, so the printed extremal type is
`(K₆ has dimension 5 ∧ K₆ has 15 edges) ∧ (K₁,₃,₃ has dimension 5 ∧ K₁,₃,₃ has 15 edges)`.

What unfolds, and is therefore not a second statement: the inline file defines its own
`UnitDistanceEmbeddable` and `HasDimension`, writes `EuclideanSpace ℝ (Fin n)` where upstream
writes the notation `ℝ^n`, and applies `HasDimension` in prefix form where upstream uses dot
notation. `ℝ^n` is declared in
`FormalConjecturesForMathlib/Geometry/Euclidean.lean` as
`scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)`. `K133` is an
`abbrev` in each file with the same body. `rfl` is what shows those copies are the same
proposition.

## Red team

The two propositions are the upstream ones. Neither is a weakening, a vacuous implication, or
a shift of binders, vertex type, edge-count function, or part sizes.

- **Binders.** `dimension_five` and `dimension_five_extremal` are closed. The `#check` output
  shows no `Fintype`, `DecidableEq`, or degree hypothesis on either type. Upstream's
  `HasDimension` is declared in `namespace SimpleGraph` under
  `variable {α : Type*} [Fintype α] [DecidableEq α]`; those variables are on `α`, and `α` does
  not occur in the definition. The elaborated theorem types have the same shape as the inline
  `{V : Type*} (G : SimpleGraph V) (n : ℕ)`.
- **`Fin n` and `V`.** The least-edge set quantifies over `SimpleGraph (Fin n)` on both sides.
  `HasDimension` itself is polymorphic in the vertex type. The extremal half applies it to
  `completeGraph (Fin 6)` and to `K133`, whose vertices are `Σ i : Fin 3, Fin (![1, 3, 3] i)`,
  the same sigma type upstream uses.
- **`ncard` and `card`.** Both sides use `G.edgeSet.ncard`. `edgeSet` is a `Set (Sym2 V)`
  (`SimpleGraph.Basic`). `Set.ncard` is `ENat.toNat ∘ encard`; Mathlib's docstring gives it
  the value `0` on an infinite set. `rfl` already means both sides use this function, including
  on `K₆` and on `K133`. The quantified graphs have vertex type `Fin n`, so the comparison
  with `Finset.card` is about a finite `Sym2`, where `ncard` is the edge count rather than
  that junk value.
- **`K133` part sizes.** Both abbrevs are
  `SimpleGraph.completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)`.
  Mathlib's `![1, 3, 3]` is `vecCons 1 (vecCons 3 (vecCons 3 vecEmpty))`, so index `0` is `1`,
  index `1` is `3`, and index `2` is `3`. `completeMultipartiteGraph` is
  `.comap Sigma.fst ⊤`: two vertices are adjacent exactly when their part indices differ.
  The extremal proposition mentions `K133`, and `rfl` identified that proposition with
  upstream, so the elaborated part-size vector is the same term.
- **Vacuity.** `DimensionFive` is an `IsLeast`: `15` is in the set and is a lower bound.
  `DimensionFiveExtremal` is a conjunction of four facts about two named graphs. Neither is
  an implication, so neither can be true because a hypothesis is false.

`lake exe fidelity` reports exactly five obligations, all discharged, and no hypothesis-drop
skip (the two claims have no `Prop` binders):

```text
closed claim ...DimensionFive ← ...DimensionFive.witness
definition ...UnitDistanceEmbeddable ← ...UnitDistanceEmbeddable.separating
definition ...HasDimension ← ...HasDimension.separating
definition ...K133 ← ...K133.separating
closed claim ...DimensionFiveExtremal ← ...DimensionFiveExtremal.witness
fidelity: 5 obligation(s) discharged
```

The audit checks that each companion mentions its subject, or a local constant the subject
mentions, and is not `True`. It does not check that the companion is true or that it is the
right example. That part was read, and four of the five were proved in `tmp/Companions.lean`.

```sh
~/.elan/bin/lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false tmp/Companions.lean
```

Exit code 0. Each of the four proofs depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

| Companion | What it asserts | Status |
|---|---|---|
| `UnitDistanceEmbeddable.separating` | Some injective placement puts every edge at distance 1 and also puts some non-edge at distance 1. This is the looser reading (a unit-distance representation), exhibited against the stricter "distance 1 implies adjacency". | Proved. The witness is an edge on `Fin 3` placed at `0` and `1` in `ℝ¹`, with the third vertex at `2`. |
| `HasDimension.separating` | Some graph with an edge is representable in `ℝ⁴` and does not have dimension 4. The edge requirement keeps the empty graph, which is representable in every dimension, from being the only example. | Proved. The witness is `K₂`: representable in `ℝ⁴`, and dimension 1, so 4 is not least. |
| `K133.separating` | Two distinct vertices of `K133` are not adjacent. The docstring's nearest wrong reading is the complete graph on the same seven vertices, which is what remains if the `Sigma.fst` pullback is dropped. | Proved, by two vertices of part index 1. |
| `DimensionFive.witness` | Some `SimpleGraph (Fin n)` has dimension 5 and `edgeSet.ncard = 15`. That is the membership half of `IsLeast`. | Not proved. Discharging it is the attainment half of the theorem, which is the rest of this project. The proposition is that statement, not `True`. |
| `DimensionFiveExtremal.witness` | `K₆` and `K133` are not isomorphic. The claim has no hypotheses; the degeneracy it guards is the two names denoting one graph. | Proved, from `Fintype.card (Fin 6) = 6` and `Fintype.card` of the sigma type equal to 7. That proof rewrites part index 2 to 3 and then `decide`s the sum. The separating proof rewrites part index 1 to 3. |

`K133.separating` is evidence that the graph is not complete. A different part vector with some
part of size at least 2 would still have a non-edge, so this companion is not what locks
`![1, 3, 3]`. The abbrev text and the `rfl` do that. The cardinality proof is a separate check
that this vector has seven vertices and that its last two parts have size 3.

`DimensionFive.witness` was judged by reading it against `IsLeast`, not by proving it. The
other four companions are kernel-checked.

## Findings

None. The inlined `DimensionFive` and `DimensionFiveExtremal` are definitionally the upstream
theorem types, and the five fidelity companions are the five obligations `lake exe fidelity`
counts.
