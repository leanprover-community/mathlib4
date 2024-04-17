/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Eric Wieser
-/
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Induced morphisms on `WithZero`

## Main definitions

* `WithZero.map'`: the `MonoidWithZero` homomorphism `WithZero G →* WithZero H` induced by
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

section lift
variable [MulOneClass G] [MulZeroOneClass H]

-- See note [partially-applied ext lemmas]
@[ext high]
theorem monoidWithZeroHom_ext ⦃f g : WithZero G →*₀ H⦄
    (h : f.toMonoidHom.comp coeMonoidHom = g.toMonoidHom.comp coeMonoidHom) :
    f = g :=
  DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : G) => DFunLike.congr_fun h g

/-- The (multiplicative) universal property of `WithZero` -/
@[simps! symm_apply_apply]
noncomputable nonrec def lift' : (G →* H) ≃ (WithZero G →*₀ H) where
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
  right_inv _ := monoidWithZeroHom_ext rfl

lemma lift'_zero (f : G →* H) : lift' f (0 : WithZero G) = 0 := rfl

@[simp] lemma lift'_coe (f : G →* H) (x : G) : lift' f (x : WithZero G) = f x := rfl

theorem lift'_unique (f : WithZero G →*₀ H) : f = lift' (f.toMonoidHom.comp coeMonoidHom) :=
  (lift'.apply_symm_apply f).symm

end lift

variable [MulOneClass G] [MulOneClass H]

/-- The `MonoidWithZero` homomorphism `WithZero G →* WithZero H` induced by a monoid homomorphism
  `f : G →* H`. -/
noncomputable def map' (f : G →* H) : WithZero G →*₀ WithZero H := lift' (coeMonoidHom.comp f)

lemma map'_zero (f : G →* H) : map' f 0 = 0 := rfl

@[simp]
lemma map'_coe (f : G →* H) (x : G) : map' f (x : WithZero G) = f x := rfl

@[simp]
theorem map'_id : map' (MonoidHom.id H) = MonoidHom.id (WithZero H) := by
  ext x
  induction x using WithOne.cases_on <;> rfl

variable {M : Type*} [MulOneClass M]

theorem map'_map'  (f : G →* H) (g : H →* M) (x) : map' g (map' f x) = map' (g.comp f) x := by
  induction x using WithOne.cases_on <;> rfl

@[simp]
theorem map'_comp (f : G →* H) (g : H →* M) : map' (g.comp f) = (map' g).comp (map' f) :=
  MonoidWithZeroHom.ext fun x => (map'_map' f g x).symm

end WithZero
