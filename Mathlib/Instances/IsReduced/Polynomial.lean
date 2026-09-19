/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Instance `IsReduced R[X]`
If `R` is reduced, so is `R[X].
-/

open Polynomial

public instance {R : Type*} [Semiring R] [IsReduced R] : IsReduced R[X] := by
  constructor
  rintro p ⟨n, hn⟩
  contrapose! hn
  rw [← Polynomial.leadingCoeff_ne_zero] at *
  grind [eq_zero_of_pow_eq_zero, leadingCoeff_pow']
