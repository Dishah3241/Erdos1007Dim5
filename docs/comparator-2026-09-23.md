# Comparator run, 2026-09-23

Comparator checks that `Solution.lean` proves exactly the statement in `Challenge.lean`, with only the
permitted axioms. It then replays the proof through two independent kernels.

- **Tree:** commit `af9c6a9`, whose `Solution` imports the local `GraphDimension` at `2e798b7`.
- **`comparator.json`:**
  - target `Erdos1007Dim5.Palomar.target`: the conjunction of `dimension_five` and `dimension_five_extremal`
  - permitted axioms `propext`, `Quot.sound`, `Classical.choice`
  - `enable_nanoda: true`
- **Tools:** the same builds as rung 1's run (`../Erdos1007/docs/comparator-2026-09-22.md`):
  - Comparator `c0c5a52`
  - `lean4export` `15f6055`
  - NanoDa `3a24072`
- **Sandbox:** none. The run used `fake-landrun.sh`, because landrun is Linux-only. This checks the mathematics,
  not isolation; Palomar re-runs it sandboxed.
- **Before publishing:** `GraphDimension` must become a git dependency pinned to a 40-character revision, and
  Comparator must run again on that tree.

## Result

```text
Building Challenge   … Build completed successfully (2385 jobs).
Exporting … Erdos1007Dim5.Palomar.target … from Challenge
Building Solution    … Build completed successfully (2762 jobs).
Exporting … Erdos1007Dim5.Palomar.target … from Solution
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The only warning in the `Challenge` build is the advertised hole: `Challenge.lean:155`,
`declaration uses 'sorry'`.

## Command

```sh
COMPARATOR_LANDRUN=~/src/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=~/src/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
COMPARATOR_NANODA=~/src/nanoda_lib/target/release/nanoda_bin \
  lake env ~/src/comparator/.lake/build/bin/comparator comparator.json
```
