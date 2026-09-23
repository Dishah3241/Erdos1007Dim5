/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Finset.Card

/-!
# Erdős 1007, dimension five: fifteen edges, attained by K6 and K1,3,3

The Mathlib-only statement source. `Challenge.lean` is **generated** from this file: everything
above the closing proof-link note, concatenated with `scripts/palomar-challenge-footer.txt`.
Regenerate with `scripts/check-palomar-challenge.sh --update`, and CI fails when the two diverge.
Drift is therefore impossible by construction rather than by discipline.

Consequences to respect:

* this file imports **only Mathlib**, because `Challenge.lean` inherits its imports and Palomar
  requires that isolation;
* it declares propositions and contains no proofs — `InlineErdos1007Dim5Proof` proves them;
* a mathematician must be able to read it alone, so inline the relevant predicate rather than
  naming one declared elsewhere;
* every closed proposition carries a `.witness`, every non-dependent hypothesis of one carries
  a `.drop<Tag>`, and every definition a `.separating`, checked by `lake exe fidelity`.

The content below is a worked illustration, to be replaced by the target during Stage 1. The
mathematics is deliberately trivial; the shape of the declarations is the point.
-/

@[expose] public section

namespace Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

/-- Every two distinct elements of `S` are coprime. -/
def PairwiseCoprime (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

/-- Separating example for `PairwiseCoprime`, required by `lake exe fidelity`.

The nearest plausible wrong definition is distinctness: elements merely pairwise different. This
asserts a set that is pairwise distinct and not pairwise coprime, separating the two notions
rather than respelling one. Without it a development could be about distinctness throughout,
because no other check inspects what a definition means. -/
def PairwiseCoprime.separating : Prop :=
  ∃ S : Finset ℕ, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ≠ b) ∧ ¬ PairwiseCoprime S

/-- Any two distinct elements of `{2, 3, 5}` are coprime. -/
def SmallPrimesCoprime : Prop :=
  ∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b ∈ ({2, 3, 5} : Finset ℕ), a ≠ b → Nat.Coprime a b

/-- Dropping membership of the first element leaves a false statement: `4` and `2` are distinct,
`2` lies in the set, and they are not coprime. -/
def SmallPrimesCoprime.drop1 : Prop :=
  ¬ ∀ a : ℕ, ∀ b ∈ ({2, 3, 5} : Finset ℕ), a ≠ b → Nat.Coprime a b

/-- Dropping membership of the second element leaves a false statement: `2` and `4` are distinct,
`2` lies in the set, and they are not coprime. -/
def SmallPrimesCoprime.drop3 : Prop :=
  ¬ ∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b : ℕ, a ≠ b → Nat.Coprime a b

/-- Dropping distinctness leaves a false statement: `2` is in the set and not coprime to itself. -/
def SmallPrimesCoprime.drop4 : Prop :=
  ¬ ∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b ∈ ({2, 3, 5} : Finset ℕ), Nat.Coprime a b

/-- Satisfiability witness for `SmallPrimesCoprime`, required by `lake exe fidelity`.

A claim whose hypotheses cannot be jointly satisfied is vacuously true, and vacuous truth passes
`lake build`, `lake exe axioms`, and Comparator alike. This asserts that `PairwiseCoprime` holds
of a set with more than one element, and that `SmallPrimesCoprime` itself holds, so the claim
constrains something that exists. A witness taking the empty set would meet the letter of the
obligation and none of its purpose, which is why the cardinality bound is part of the statement. -/
def SmallPrimesCoprime.witness : Prop :=
  ∃ S : Finset ℕ, PairwiseCoprime S ∧ 1 < S.card ∧ SmallPrimesCoprime

end Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

/-!
## Formal proof

Proved in `InlineErdos1007Dim5Proof`.

* `separating` → `separating.proof`
* `SmallPrimesCoprime` → `SmallPrimesCoprime.proof`
* `drop1` → `drop1.proof`
* `drop3` → `drop3.proof`
* `drop4` → `drop4.proof`
* `witness` → `witness.proof`
-/
