/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

## Main declarations

* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/

namespace Int

@[simp, norm_cast]
theorem cast_mul [Ring α] : -- FIXME: NonAssocRing
    ∀ m n, ((m * n : ℤ) : α) = m * n := fun m =>
  Int.inductionOn' m 0 (by simp)
    (fun k _ ih n => by simp [add_mul, ih])
    (fun k _ ih n => by simp [sub_mul, ih])
