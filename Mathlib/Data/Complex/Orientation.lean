/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module data.complex.orientation
! leanprover-community/mathlib commit cd8fafa2fac98e1a67097e8a91ad9901cfde48af
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Orientation

/-!
# The standard orientation on `ℂ`.

This had previously been in `linear_algebra.orientation`,
but keeping it separate results in a significant import reduction.
-/


namespace Complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.Orientation
#align complex.orientation Complex.orientation

end Complex

