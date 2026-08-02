/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import SOS.Core
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Boolean SOS certificate checks

Characterization of the Mathlib-free engine's executable certificate checker.
-/

public section

namespace SOS

open CPoly

/-- `checks goal gs ps = true` is equivalent to the polynomial identity
together with the bounds, coefficient-nonnegativity, and length matches. -/
theorem Certificate.checks_iff {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n Rat)) (ps : List (CMvPolynomial n Rat)) :
    c.checks goal gs ps = true ↔
      Certificate.indicesInBounds c.sigmas gs.length = true ∧
      (∀ pair ∈ c.sigmas, pair.2.coeffsNonneg = true) ∧
      c.eqCofs.length = ps.length ∧
      goal.target = c.toPoly gs ps := by
  unfold Certificate.checks
  simp [decide_eq_true_eq, and_assoc, List.all_eq_true]

end SOS
