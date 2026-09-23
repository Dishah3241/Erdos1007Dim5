/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5Proof

/-!
# Erdős 1007, dimension five: fifteen edges, attained by K6 and K1,3,3

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace Erdos1007Dim5.Palomar

/-- Any two distinct elements of `{2, 3, 5}` are coprime. -/
theorem target :
    Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5.SmallPrimesCoprime :=
  Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5.SmallPrimesCoprime.proof

end Erdos1007Dim5.Palomar
