/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.clifford_algebra.star
! leanprover-community/mathlib commit 4d66277cfec381260ba05c68f9ae6ce2a118031d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Star structure on `clifford_algebra`

This file defines the "clifford conjugation", equal to `reverse (involute x)`, and assigns it the
`star` notation.

This choice is somewhat non-canonical; a star structure is also possible under `reverse` alone.
However, defining it gives us access to constructions like `unitary`.

Most results about `star` can be obtained by unfolding it via `clifford_algebra.star_def`.

## Main definitions

* `clifford_algebra.star_ring`

-/


variable {R : Type _} [CommRing R]

variable {M : Type _} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

instance : StarRing (CliffordAlgebra Q) where
  unit x := reverse (involute x)
  star_involutive x := by
    simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute]
  star_mul x y := by simp only [map_mul, reverse.map_mul]
  star_add x y := by simp only [map_add]

theorem star_def (x : CliffordAlgebra Q) : star x = reverse (involute x) :=
  rfl
#align clifford_algebra.star_def CliffordAlgebra.star_def

theorem star_def' (x : CliffordAlgebra Q) : star x = involute (reverse x) :=
  reverse_involute _
#align clifford_algebra.star_def' CliffordAlgebra.star_def'

@[simp]
theorem star_ι (m : M) : star (ι Q m) = -ι Q m := by rw [star_def, involute_ι, map_neg, reverse_ι]
#align clifford_algebra.star_ι CliffordAlgebra.star_ι

/-- Note that this not match the `star_smul` implied by `star_module`; it certainly could if we
also conjugated all the scalars, but there appears to be nothing in the literature that advocates
doing this. -/
@[simp]
theorem star_smul (r : R) (x : CliffordAlgebra Q) : star (r • x) = r • star x := by
  rw [star_def, star_def, map_smul, map_smul]
#align clifford_algebra.star_smul CliffordAlgebra.star_smul

@[simp]
theorem star_algebraMap (r : R) :
    star (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (CliffordAlgebra Q) r := by
  rw [star_def, involute.commutes, reverse.commutes]
#align clifford_algebra.star_algebra_map CliffordAlgebra.star_algebraMap

end CliffordAlgebra

