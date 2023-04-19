/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.products
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Pi
import Mathbin.Algebra.Category.Module.Basic

/-!
# The concrete products in the category of modules are products in the categorical sense.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

/-- The product cone induced by the concrete product. -/
def productCone : Fan Z :=
  Fan.mk (ModuleCat.of R (∀ i : ι, Z i)) fun i => (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i)
#align Module.product_cone ModuleCat.productCone

/-- The concrete product cone is limiting. -/
def productConeIsLimit : IsLimit (productCone Z)
    where
  lift s := (LinearMap.pi fun j => s.π.app ⟨j⟩ : s.pt →ₗ[R] ∀ i : ι, Z i)
  fac s j := by
    cases j
    tidy
  uniq s m w := by
    ext (x i)
    exact LinearMap.congr_fun (w ⟨i⟩) x
#align Module.product_cone_is_limit ModuleCat.productConeIsLimit

-- While we could use this to construct a `has_products (Module R)` instance,
-- we already have `has_limits (Module R)` in `algebra.category.Module.limits`.
variable [HasProduct Z]

/-- The categorical product of a family of objects in `Module`
agrees with the usual module-theoretical product.
-/
noncomputable def piIsoPi : ∏ Z ≅ ModuleCat.of R (∀ i, Z i) :=
  limit.isoLimitCone ⟨_, productConeIsLimit Z⟩
#align Module.pi_iso_pi ModuleCat.piIsoPi

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
theorem piIsoPi_inv_kernel_ι (i : ι) :
    (piIsoPi Z).inv ≫ Pi.π Z i = (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) :=
  limit.isoLimitCone_inv_π _ _
#align Module.pi_iso_pi_inv_kernel_ι ModuleCat.piIsoPi_inv_kernel_ι

@[simp, elementwise]
theorem piIsoPi_hom_ker_subtype (i : ι) :
    (piIsoPi Z).hom ≫ (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) = Pi.π Z i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)
#align Module.pi_iso_pi_hom_ker_subtype ModuleCat.piIsoPi_hom_ker_subtype

end ModuleCat

