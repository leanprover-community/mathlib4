/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Orientation

#align_import data.complex.orientation from "leanprover-community/mathlib"@"cd8fafa2fac98e1a67097e8a91ad9901cfde48af"

/-!
# The standard orientation on `ℂ`.

This had previously been in `LinearAlgebra.Orientation`,
but keeping it separate results in a significant import reduction.
-/


namespace Complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.orientation
#align complex.orientation Complex.orientation

end Complex
