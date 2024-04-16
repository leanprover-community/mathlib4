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

variable {G H : Type*}

/-- If `G` is a monoid and `x y : WithZero G` have a nonzero product, then
  `unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy)`  -/
theorem unzero_mul [Mul G] {x y : WithZero G} (hxy : x * y ≠ 0) :
    unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy) := by
  simp only [← coe_inj, coe_mul, coe_unzero]

/-- Coercion as a monoid hom -/
@[simps apply]
def coeMonoidHom [MulOneClass G] : G →* WithZero G where
  toFun        := (↑)
  map_one'     := rfl
  map_mul' _ _ := rfl

/-- The (multiplicative) universal property of `WithZero` -/
noncomputable nonrec def lift' [MulOneClass G] [MonoidWithZero H] :
    (G →* H) ≃ (WithZero G →*₀ H) where
  toFun f :=
    { toFun := fun
        | 0 => 0
        | (g : G) => f g
      map_zero' := rfl
      map_one' := map_one f
      map_mul' := fun
        | 0, _ => (zero_mul _).symm
        | (_ : G), 0 => (mul_zero _).symm
        | (_ : G), (_ : G) => map_mul f _ _ }
  invFun F := F.toMonoidHom.comp coeMonoidHom
  left_inv _ := rfl
  right_inv f := DFunLike.ext _ _ fun
    | 0 => (map_zero f).symm
    | (_ : G) => rfl

variable [MulOneClass G] [Monoid H]

/-- The `MonoidWithZero` homomorphism `WithZero G →* WithZero H` induced by a monoid homomorphism
  `f : G →* H`. -/
noncomputable def map' (f : G →* H) : WithZero G →*₀ WithZero H := lift' (coeMonoidHom.comp f)

lemma map'_zero (f : G →* H) : map' f 0 = 0 := rfl

lemma map'_coe (f : G →* H) (x : G) : map' f (x : WithZero G) = f x := rfl

end WithZero
