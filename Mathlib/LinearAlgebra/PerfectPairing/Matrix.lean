/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module -- shake: keep-all

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

deprecated_module (since := "2025-08-16")

/-!
# Perfect pairings and matrices

The file contains results connecting perfect pairings and matrices.

## Main definitions
* `Matrix.toPerfectPairing`: regard an invertible matrix as a perfect pairing.

-/

public section

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
  (A : Matrix n n R) (h : Invertible A)

/-- We may regard an invertible matrix as a perfect pairing. -/
@[deprecated "No replacement" (since := "2025-08-16")]
lemma toPerfectPairing : ((A.toLinearEquiv' h).trans (dotProductEquiv R n)).IsPerfPair where
  bijective_left := LinearEquiv.bijective _
  bijective_right := LinearMap.IsPerfPair.bijective_right _

@[deprecated "No replacement" (since := "2025-08-16")]
lemma toPerfectPairing_apply_apply (v w : n → R) :
    ((A.toLinearEquiv' h).trans (dotProductEquiv R n)) v w = A *ᵥ v ⬝ᵥ w :=
  rfl

end Matrix
