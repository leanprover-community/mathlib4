/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Induced morphisms on `WithZero`

## Main definitions

* `WithOne.coeMonoidHom`: the `MonoidWithZero` homomorphism `WithZero G →* WithZero H` induced by
  a monoid homomorphism `f : G →* H`.
-/

namespace WithZero

variable {G H : Type*} [Monoid G] [Monoid H]

/-- If `G` is a monoid and `x y : WithZero G` have a nonzero product, then
  `unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy)`  -/
theorem unzero_mul {x y : WithZero G} (hxy : x * y ≠ 0) :
    unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy) := by
  simp only [← coe_inj, coe_mul, coe_unzero]

/-- The `MonoidWithZero` homomorphism `WithZero G →* WithZero H` induced by a monoid homomorphism
  `f : G →* H`. -/
noncomputable def coeMonoidHom (f : G →* H) [DecidableEq (WithZero G)] :
    WithZero G →*₀ WithZero H where
  toFun x   := if hx : x = 0 then 0 else f (unzero hx)
  map_zero' := by simp only [dif_pos]
  map_one'  := by
    have h1 : (1 : WithZero G) ≠ 0 := one_ne_zero
    have h := Classical.choose_spec (ne_zero_iff_exists.mp h1)
    simp only [dif_neg h1]
    simp_rw [← coe_one] at h ⊢
    rw [coe_inj, unzero_coe, f.map_one]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · simp only [dif_pos hxy]
      cases' zero_eq_mul.mp (Eq.symm hxy) with hx hy
      · rw [dif_pos hx, MulZeroClass.zero_mul]
      · rw [dif_pos hy, MulZeroClass.mul_zero]
    · simp only
      rw [dif_neg hxy, dif_neg (left_ne_zero_of_mul hxy), dif_neg (right_ne_zero_of_mul hxy), ←
        coe_mul, coe_inj, ← f.map_mul, unzero_mul hxy]

end WithZero
