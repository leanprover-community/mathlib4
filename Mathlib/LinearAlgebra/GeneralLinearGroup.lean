/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Module.Equiv

#align_import linear_algebra.general_linear_group from "leanprover-community/mathlib"@"2705404e701abc6b3127da906f40bae062a169c9"

/-!
# The general linear group of linear maps

The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See also `Matrix.GeneralLinearGroup`

## Main definitions

* `LinearMap.GeneralLinearGroup`

-/


variable (R M : Type*)

namespace LinearMap

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- The group of invertible linear maps from `M` to itself -/
@[reducible]
def GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ
#align linear_map.general_linear_group LinearMap.GeneralLinearGroup

namespace GeneralLinearGroup

variable {R M}

-- Porting note: This is not necessary anymore
-- instance : CoeFun (GeneralLinearGroup R M) fun _ ↦ M → M := by infer_instance

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m ↦ show (f.inv * f.val) m = m by erw [f.inv_val]; simp
                                                      -- ⊢ ↑1 m = m
                                                                       -- 🎉 no goals
    right_inv := fun m ↦ show (f.val * f.inv) m = m by erw [f.val_inv]; simp }
                                                       -- ⊢ ↑1 m = m
                                                                        -- 🎉 no goals
#align linear_map.general_linear_group.to_linear_equiv LinearMap.GeneralLinearGroup.toLinearEquiv

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M →ₗ[R] M)
  val_inv := LinearMap.ext fun _ ↦ f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ ↦ f.symm_apply_apply _
#align linear_map.general_linear_group.of_linear_equiv LinearMap.GeneralLinearGroup.ofLinearEquiv

variable (R M)

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  left_inv f := by ext; rfl
                   -- ⊢ ↑↑(ofLinearEquiv (toLinearEquiv f)) x✝ = ↑↑f x✝
                        -- 🎉 no goals
  right_inv f := by ext; rfl
                    -- ⊢ ↑(toLinearEquiv (ofLinearEquiv f)) x✝ = ↑f x✝
                         -- 🎉 no goals
  map_mul' x y := by ext; rfl
                     -- ⊢ ↑(Equiv.toFun { toFun := toLinearEquiv, invFun := ofLinearEquiv, left_inv := …
                          -- 🎉 no goals
#align linear_map.general_linear_group.general_linear_equiv LinearMap.GeneralLinearGroup.generalLinearEquiv

@[simp]
theorem generalLinearEquiv_to_linearMap (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f : M →ₗ[R] M) = f := by ext; rfl
                                                     -- ⊢ ↑↑(↑(generalLinearEquiv R M) f) x✝ = ↑↑f x✝
                                                          -- 🎉 no goals
#align linear_map.general_linear_group.general_linear_equiv_to_linear_map LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap

@[simp]
theorem coeFn_generalLinearEquiv (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f) = (f : M → M) := rfl
#align linear_map.general_linear_group.coe_fn_general_linear_equiv LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv

end GeneralLinearGroup

end LinearMap
