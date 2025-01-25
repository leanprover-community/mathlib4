/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib

/-!
# Fredholm operators

TODO: create a doc-string here, once time comes

## TODO
- generalise to e.g. TVS: proving things about them will require e.g. a version
of the Hahn-Banach theorem for TVS, which does not exist yet

-/

-- Let 𝕜 be a field, and X, Y and Z be normed spaces over 𝕜.
variable {𝕜: Type*} [NormedField 𝕜]
  {X Y Z: Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {S T : X →L[𝕜] Y}

open FiniteDimensional

variable (T) in
/-- A bounded linear operator `T: X → Y` is Fredholm iff its kernel and cokernel
are finite-dimensional (and it has closed range?). -/
def IsFredholm : Prop :=
  FiniteDimensional 𝕜 (LinearMap.ker T) ∧ FiniteDimensional 𝕜 (Y ⧸ LinearMap.range T)

-- TODO: in the future
/-- If X and Y are complete, closedness of `range T` is automatic for Fredholm operators. -/
theorem IsFredholm.closedRange_of_completeSpace [CompleteSpace X] [CompleteSpace Y] (hT : IsFredholm T) : IsClosed (LinearMap.range T: Set Y) := sorry
