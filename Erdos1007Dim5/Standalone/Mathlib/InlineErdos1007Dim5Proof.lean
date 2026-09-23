/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

/-!
# Erdős 1007, dimension five: fifteen edges, attained by K6 and K1,3,3

The proof sibling. Unlike its statement module this may import the development, and it is the one
explicit exception to the standalone isolation rule.

`lake exe proof-links` requires, for every closed proposition `C` in the statement module, a
theorem named `C.proof` whose type is exactly `C` applied to the statement's own parameter
telescope. Renaming or deleting one fails the audit.

Each proof opens with `change`, spelling out the proposition it discharges. That keeps the proof
readable without chasing the definition, and it fails loudly if the statement moves underneath it.
`unfold` before `decide` is required because instance synthesis does not see through a `def`, even
an exposed one.
-/

public section

namespace Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

/-- `{2, 4}` is pairwise distinct and not pairwise coprime, separating coprimality from mere
distinctness. -/
theorem PairwiseCoprime.separating.proof : PairwiseCoprime.separating := by
  change ∃ S : Finset ℕ, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ≠ b) ∧ ¬ PairwiseCoprime S
  refine ⟨{2, 4}, fun _ _ _ _ h => h, ?_⟩
  unfold PairwiseCoprime
  decide

theorem SmallPrimesCoprime.proof : SmallPrimesCoprime := by
  change ∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b ∈ ({2, 3, 5} : Finset ℕ), a ≠ b → Nat.Coprime a b
  decide

theorem SmallPrimesCoprime.drop1.proof : SmallPrimesCoprime.drop1 := by
  change ¬ ∀ a : ℕ, ∀ b ∈ ({2, 3, 5} : Finset ℕ), a ≠ b → Nat.Coprime a b
  intro hyp
  have hmem : (2 : ℕ) ∈ ({2, 3, 5} : Finset ℕ) := by decide
  have hne : (4 : ℕ) ≠ 2 := by decide
  have hnot : ¬ Nat.Coprime 4 2 := by decide
  exact absurd (hyp 4 2 hmem hne) hnot

theorem SmallPrimesCoprime.drop3.proof : SmallPrimesCoprime.drop3 := by
  change ¬ ∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b : ℕ, a ≠ b → Nat.Coprime a b
  intro hyp
  have hmem : (2 : ℕ) ∈ ({2, 3, 5} : Finset ℕ) := by decide
  have hne : (2 : ℕ) ≠ 4 := by decide
  have hnot : ¬ Nat.Coprime 2 4 := by decide
  exact absurd (hyp 2 hmem 4 hne) hnot

theorem SmallPrimesCoprime.drop4.proof : SmallPrimesCoprime.drop4 := by
  change ¬ ∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b ∈ ({2, 3, 5} : Finset ℕ), Nat.Coprime a b
  intro hyp
  have hmem : (2 : ℕ) ∈ ({2, 3, 5} : Finset ℕ) := by decide
  have hnot : ¬ Nat.Coprime 2 2 := by decide
  exact absurd (hyp 2 hmem 2 hmem) hnot

/-- `{2, 3}` is pairwise coprime and has more than one element, so the claim is not vacuous. -/
theorem SmallPrimesCoprime.witness.proof : SmallPrimesCoprime.witness := by
  change ∃ S : Finset ℕ, PairwiseCoprime S ∧ 1 < S.card ∧ SmallPrimesCoprime
  refine ⟨{2, 3}, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold PairwiseCoprime
    decide
  · decide
  · exact SmallPrimesCoprime.proof

end Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5
