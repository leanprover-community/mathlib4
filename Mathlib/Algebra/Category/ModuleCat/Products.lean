/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic

#align_import algebra.category.Module.products from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The concrete products in the category of modules are products in the categorical sense.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCatMax.{v, w} R)

set_option linter.uppercaseLean3 false

/-- The product cone induced by the concrete product. -/
def productCone : Fan Z :=
  Fan.mk (ModuleCat.of R (∀ i : ι, Z i)) fun i => (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i)
#align Module.product_cone ModuleCat.productCone

/-- The concrete product cone is limiting. -/
def productConeIsLimit : IsLimit (productCone Z) where
  lift s := (LinearMap.pi fun j => s.π.app ⟨j⟩ : s.pt →ₗ[R] ∀ i : ι, Z i)
  fac s j := by
    cases j
    -- ⊢ (fun s => LinearMap.pi fun j => NatTrans.app s.π { as := j }) s ≫ NatTrans.a …
    aesop
    -- 🎉 no goals
  uniq s m w := by
    ext x
    -- ⊢ ↑m x = ↑((fun s => LinearMap.pi fun j => NatTrans.app s.π { as := j }) s) x
    funext i
    -- ⊢ ↑m x i = ↑((fun s => LinearMap.pi fun j => NatTrans.app s.π { as := j }) s)  …
    exact LinearMap.congr_fun (w ⟨i⟩) x
    -- 🎉 no goals
#align Module.product_cone_is_limit ModuleCat.productConeIsLimit

-- While we could use this to construct a `HasProducts (ModuleCat R)` instance,
-- we already have `HasLimits (ModuleCat R)` in `Algebra.Category.ModuleCat.Limits`.
variable [HasProduct Z]

/-- The categorical product of a family of objects in `ModuleCat`
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
