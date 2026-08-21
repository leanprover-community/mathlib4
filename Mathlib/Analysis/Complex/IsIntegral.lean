/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao, Snir Broshi
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.Algebra.Polynomial.Monic

/-!
# Integral elements of ℂ

This file proves that `Complex.I` is integral over any commutative ring `R` when `ℂ` is an
`R`-algebra.
-/

public section

open Polynomial

namespace Complex

theorem isIntegral_I (R : Type*) [CommRing R] [Algebra R ℂ] : IsIntegral R I :=
  ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, by simp⟩

@[deprecated (since := "2026-08-06")] alias isIntegral_int_I := isIntegral_I

@[deprecated (since := "2026-08-06")] alias isIntegral_rat_I := isIntegral_I

end Complex
