# Erdos1007Dim5 working rules

`README.md` states the target and the current stage. `../../AGENTS.md` holds the workspace rules
and governs here too — read it first. `../../docs/PLAYBOOK.md` holds the pipeline. This file
covers only what is specific to a Lean project repository.

Adapted from `AGENTS.md` in [gaearon/conway-refinement][ref] (Apache-2.0).

[ref]: https://github.com/gaearon/conway-refinement

## Mathematical standard

- Lean is the authority for what is proved. State exact quantifiers, ambient hypotheses, zero and
  degenerate cases, inequality direction, and equality orientation.
- Use established terminology in declaration names, statements, docstrings, and the blueprint.
  `blueprint/terminology/FIELD.md` records this project's vocabulary and its sources.
- Follow Mathlib spelling in module paths, declaration names, and API references. Reader-facing
  prose follows the field map; cited titles stay verbatim.
- A theorem attributed to a source retains every mathematically relevant source hypothesis. A
  stronger generalization is a separate declaration, identified as such.
- Validate a new definition with characteristic lemmas and a separating example distinguishing it
  from the nearest plausible wrong definition. **Compilation is not fidelity.**
- Search pinned Mathlib before introducing a definition or a substantial proof. Reuse its
  namespace, notation, theorem shape, and API where the mathematics agrees. Never edit a pinned
  dependency in place.
- No declaration under `Erdos1007Dim5/` may use `sorry`, directly or transitively. The only admitted
  axioms are `propext`, `Classical.choice`, and `Quot.sound`, enforced by `lake exe axioms`. The
  root `Challenge.lean` may contain only its advertised hole.

## Architecture

Modules are organized by mathematical object. General mathematics mirrors Mathlib's top-level
areas: `Algebra/`, `Analysis/`, `Combinatorics/`, `Data/`, `FieldTheory/`, `LinearAlgebra/`,
`NumberTheory/`, `Order/`, `RingTheory/`, `SetTheory/`, `Topology/`. The project's own spine lives
in its own subdirectories, listed in order in `subjectRoots` in `scripts/Layering.lean`.

Imports run from general mathematics towards the subject. `Examples/`, `Standalone/`, and local
`Tests/` are leaves. `Tests/` holds compiled clients of nearby public APIs; `Examples/` holds
mathematics worth reading. `lake exe layering` enforces this.

Every file uses the module system: begin with `module`, `public import` exactly when an imported
name occurs in an exported type, and put exported declarations in a `public section`. Import the
module that directly provides each name. `lake build` is authoritative because the `Erdos1007Dim5.*`
glob compiles every source file, so an orphaned module still fails.

Keep pinned Lean and Mathlib revisions fixed during a mathematical change. A dependency update is
its own reviewed change.

## Statement entry points

Top-level files in `Erdos1007Dim5/Standalone/Mathlib/` are claims meant to be read by a mathematician
as single files. `InlineErdos1007Dim5.lean` is the Palomar statement source: **`Challenge.lean` is
generated from it** by `scripts/check-palomar-challenge.sh --update`, as its prefix up to the
closing proof-link note plus `scripts/palomar-challenge-footer.txt`. Never hand-edit
`Challenge.lean`; edit the source and regenerate. CI fails when the two diverge, so statement
drift is prevented by construction rather than by discipline.

- A claim file states a substantive result in immediately recognizable language. A reader must not
  need to follow a project definition to decide what it says: inline the relevant predicate or give
  an exact elementary characterization in the file.
- Keep narration short. Docstrings describe the object or conclusion, never implementation history,
  proof status, or editorial plans.
- A sibling `FooProof.lean` supplies the proof of every closed proposition in `Foo.lean`. Move
  unrelated machinery to `Support/`.
- Statement files import **only Mathlib**. Proof siblings are the explicit exception.
- Every closed proposition carries a `.witness`; every definition carries a `.separating`.
  Every non-dependent `Prop` hypothesis of a closed proposition also carries a `.drop<Tag>`
  companion. `<Tag>` is the binder's name with each `_`-separated segment capitalized (`hdim`
  gives `dropHdim`), or its telescope index when the binder is anonymous (`drop2`); Mathlib's
  `defsWithUnderscore` linter rejects an underscore. See
  `InlineErdos1007Dim5.lean` for what each must actually accomplish. `lake exe fidelity` checks
  that witnesses and separating examples exist, are about their subject, and are not `True`, and
  that each drop companion is definitionally the negation of the claim with that hypothesis
  removed. It cannot check that a witness or a separating example is *good*, which is why those
  two stay on the semantic-review list.

Enforced by `lake exe standalone-mathlib`, `lake exe proof-links`, and `lake exe fidelity`.

## Lean style

- Keep public definition bodies opaque. Provide the characteristic, membership, coercion,
  evaluation, extensionality, and operation lemmas downstream clients need.
- Do not rely on accidental definitional equality across modules. Add a public eliminator or pass
  explicit data.
- Test public interfaces in separately compiled `Tests/` clients, including zero, degenerate, and
  nondegenerate cases where they distinguish the intended semantics.
- Prefer dependency-native notation and dot notation. Introduce syntax only for a repeated
  mathematical distinction.
- Follow Mathlib formatting, lines at most 100 characters. Do not weaken warnings or linters. A
  `@[nolint]` requires a mathematical justification and an allowlist entry.

## Workflow

1. Fix the intended statement and search the pinned dependencies.
2. Prototype uncertain mathematics in `tmp/`; keep `tmp/` empty at committed checkpoints.
3. Move only typechecked work into its semantic module, with the smallest meaningful client.
4. Run focused checks while iterating. Before a green checkpoint run every gate in
   `../../AGENTS.md`.
5. When you change an audit, extend `scripts/audit-probes.sh` so the checker must reject a
   representative bad input and name that probe.
6. Inspect the exact diff and commit one coherent change. Do not stage unrelated work.

A direct one-file check must pass the package options explicitly:

```text
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false FILE.lean
```

## This project: what Erdos1007 taught

Rung 2 of the Math workspace's ADR 0004. Scope, the proof of record and the plan are recorded in
`../../docs/research/2026-09-22-stage0-rung2-and-end-problem.md`,
`../../docs/design/rung2-blueprint.tex` and ROADMAP P3. Rung 1 hit each item below at least once.

- **The statement is inherited.** Inline upstream's `erdos_1007.variants.dimension_five` and
  `dimension_five_extremal` (pinned in `formalization.yaml`) into
  `Erdos1007Dim5/Standalone/Mathlib/InlineErdos1007Dim5.lean`. Then check agreement with upstream by
  `rfl`, run by a different model lineage from the one that inlined it (PLAYBOOK Stage 1, "When the
  statement is inherited rather than authored"). The authored-path brief does not apply.
- **The fidelity battery was built for an implication.** `dimension_five` is an `IsLeast`, and
  `dimension_five_extremal` is a conjunction about two named graphs. Before Stage 1 exits, read what
  `lake exe fidelity` demands of each shape, and write separating and drop companions that actually
  separate.
- **The library comes first.** Nodes marked `GraphDimension/…` in the blueprint belong to the shared
  library (`../../docs/design/graph-dimension-library.md`, ROADMAP P2). Rung 1's proved lemmas in
  `../Erdos1007` (Apache-2.0) are its seed. Do not re-prove a library result here.
- **Blueprint nodes name proofs.** A `\lean{}` must name the theorem that proves the node, not the
  `Prop` definition it is about. `checkdecls` passes either way.
- **Status lines link receipts.** Every stage or gate claim in `README.md` links the file or run
  that shows it.
- **The paper is a PDF.** Chaffee–Noble 2016 has no arXiv source. It is staged at
  `~/src/papers/chaffee-noble-2016/`. Read it rendered, and check any erratum against the rendered
  page (Math finding A1 withdrew a false one).
- **The hardest leaf is `K₁,₃,₃ ∉ ℝ⁴`** (Chaffee–Noble Theorem 8). Use rung 1's
  orthogonal-complement argument from the `K₃,₃ ∉ ℝ³` lower bound, not the paper's coordinate
  rotation.
- **Workers never commit** (`agent-run` forbids it); the manager lands. Model names come from
  `../../harness/run-model <run-id>`.
