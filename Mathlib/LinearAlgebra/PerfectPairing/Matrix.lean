/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Perfect pairings and matrices

The file contains results connecting perfect pairings and matrices.

## Main definitions
* `Matrix.toPerfectPairing`: regard an invertible matrix as a perfect pairing.

-/

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
  (A : Matrix n n R) (h : Invertible A)

set_option linter.deprecated false in
/-- We may regard an invertible matrix as a perfect pairing. -/
@[deprecated "No replacement" (since := "2025-08-16")]
def toPerfectPairing :
    PerfectPairing R (n → R) (n → R) :=
  ((A.toLinearEquiv' h).trans (dotProductEquiv R n)).toPerfectPairing

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2025-08-16")]
lemma toPerfectPairing_apply_apply (v w : n → R) :
    A.toPerfectPairing h v w = A *ᵥ v ⬝ᵥ w :=
  rfl

end Matrix
