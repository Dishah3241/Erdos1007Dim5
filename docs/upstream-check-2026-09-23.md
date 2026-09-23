# Upstream proof check, 2026-09-23

This record shows that the proofs prove `formal-conjectures`' own declarations, checked by the kernel against
upstream's declaration types in one environment. It covers items 2 to 4 of `formal-conjectures`' `PROOFS.md` link
checklist. `docs/upstream-check-stage1.md` checked the statements by `rfl`; this record checks the proofs.

- **`formal-conjectures`:** the dimension-five declarations as pinned in `formalization.yaml` (`2a46c7b`), built in a
  local checkout whose `1007.lean` differs from that pin only by rung 1's `formal_proof` attribute.
- **This repository:** with `GraphDimension` pinned at `05da2520de4752817cc5b19e92f4237e843af343`, fetched from
  GitHub.
- Both pin Lean `v4.33.1` and the same Mathlib.

Before `05da252`, this check could not run. `GraphDimension` defined `SimpleGraph.HasDimension`, the full name
`FormalConjecturesForMathlib` uses, so no environment could import both (Math finding A34). The library now calls
it `SimpleGraph.HasUnitDistDim`.

## The check

```lean
import FormalConjectures.ErdosProblems.«1007»
import Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5Proof

theorem upstream_dimension_five_holds :
    type_of% @Erdos1007.erdos_1007.variants.dimension_five :=
  Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5.DimensionFive.proof

theorem upstream_dimension_five_extremal_holds :
    type_of% @Erdos1007.erdos_1007.variants.dimension_five_extremal :=
  Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5.DimensionFiveExtremal.proof

#check @Erdos1007.erdos_1007.variants.dimension_five
#check @Erdos1007.erdos_1007.variants.dimension_five_extremal
#print axioms upstream_dimension_five_holds
#print axioms upstream_dimension_five_extremal_holds
```

## Command

Run from the `formal-conjectures` checkout, with this repository built at `$E`:

```sh
lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$E/.lake/build/lib/lean:$E/.lake/packages/GraphDimension/.lake/build/lib/lean\" lean Check.lean"
```

## Result

Exit 0. The only other output is a style warning that the scratch file has no module docstring.

```text
Erdos1007.erdos_1007.variants.dimension_five : IsLeast {m | ∃ n G, G.HasDimension 5 ∧ G.edgeSet.ncard = m} 15
Erdos1007.erdos_1007.variants.dimension_five_extremal : ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
    (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
  Erdos1007.K133.HasDimension 5 ∧ Erdos1007.K133.edgeSet.ncard = 15
'upstream_dimension_five_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'upstream_dimension_five_extremal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
