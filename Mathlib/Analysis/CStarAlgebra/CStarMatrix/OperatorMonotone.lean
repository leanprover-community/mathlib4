/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator-monotone functions on `CStarMatrix`

This file provides convenient access to the operator-monotonicity results
`CFC.monotone_rpow`, `CFC.log_monotoneOn`, and `CFC.monotone_sqrt` for the
unital C⋆-algebra `CStarMatrix n n A`, by:

1. Registering the real selfadjoint continuous functional calculus and the
   `ℝ`-valued non-negative spectrum class on `CStarMatrix n n A` as
   shortcut instances. Although these instances *can* be derived from
   `CStarAlgebra (CStarMatrix n n A)`, the search path through the generic
   `Matrix` typeclass diamond does not find them automatically.
2. Specialising the three operator-monotonicity lemmas to the
   `CStarMatrix` namespace, so that downstream users can discover them via
   dot-notation on `CStarMatrix n n A`.

The declarations below are stated for the unital case, since
`CStarMatrix n n A` has a `CStarAlgebra` instance only when `n` is a
finite type with decidable equality.

## Main declarations

* `CStarMatrix.monotone_rpow`: `M ↦ M ^ p` is operator monotone on
  `CStarMatrix n n A` for `p ∈ [0, 1]`.
* `CStarMatrix.log_monotoneOn`: `CFC.log` is operator monotone on the
  strictly positive elements of `CStarMatrix n n A`.
* `CStarMatrix.monotone_sqrt`: `CFC.sqrt` is operator monotone on
  `CStarMatrix n n A`.
-/

public section

set_option linter.unusedDecidableInType false

namespace CStarMatrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Shortcut instance: the unital real continuous functional calculus for
selfadjoint elements of `CStarMatrix n n A`.

This is derivable from `IsSelfAdjoint.instContinuousFunctionalCalculus`
together with the `CStarAlgebra` instance, but the typeclass search does
not find it automatically through the `Matrix` diamond. Registering it
explicitly enables ergonomic use of `CFC.rpow`, `CFC.log`, etc. -/
noncomputable instance instContinuousFunctionalCalculusRealIsSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := CStarMatrix n n A)

/-- Shortcut instance: the non-unital real continuous functional calculus for
selfadjoint elements of `CStarMatrix n n A`.

This is derivable from `IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus`
together with the `NonUnitalCStarAlgebra` instance, but the typeclass search
does not find it automatically through the `Matrix` diamond. Registering it
explicitly enables ergonomic use of `CFC.sqrt`, etc. -/
noncomputable instance instNonUnitalContinuousFunctionalCalculusRealIsSelfAdjoint :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := CStarMatrix n n A)

/-- Shortcut instance: the real spectrum of any non-negative element of
`CStarMatrix n n A` is contained in `[0, ∞)`.

This is derivable from `CStarAlgebra.instNonnegSpectrumClass` together with
the `CStarAlgebra` instance, but the typeclass search does not find it
automatically through the `Matrix` diamond. -/
noncomputable instance instNonnegSpectrumClassReal :
    NonnegSpectrumClass ℝ (CStarMatrix n n A) :=
  CStarAlgebra.instNonnegSpectrumClass (A := CStarMatrix n n A)

/-- `M ↦ M ^ p` is operator monotone on `CStarMatrix n n A` for `p ∈ [0, 1]`. -/
lemma monotone_rpow {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (fun M : CStarMatrix n n A => M ^ p) :=
  CFC.monotone_rpow hp

/-- The operator logarithm is monotone on the strictly positive elements of
`CStarMatrix n n A`. -/
lemma log_monotoneOn :
    MonotoneOn (CFC.log : CStarMatrix n n A → CStarMatrix n n A)
      {M | IsStrictlyPositive M} :=
  CFC.log_monotoneOn

/-- The operator square root is monotone on `CStarMatrix n n A`. -/
lemma monotone_sqrt :
    Monotone (CFC.sqrt : CStarMatrix n n A → CStarMatrix n n A) :=
  CFC.monotone_sqrt

end CStarMatrix
