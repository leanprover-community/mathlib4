/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Tactic.CategoryTheory.Elementwise

#align_import algebra.category.Group.biproducts from "leanprover-community/mathlib"@"234ddfeaa5572bc13716dd215c6444410a679a8e"

/-!
# The category of abelian groups has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

universe w u

namespace AddCommGroupCat
set_option linter.uppercaseLean3 false -- `AddCommGroup`

-- As `AddCommGroupCat` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts AddCommGroupCat :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts AddCommGroupCat :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `AddCommGroupCat`, using
`AddCommGroupCat.of (G × H)`.
-/
@[simps cone_pt isLimit_lift]
def binaryProductLimitCone (G H : AddCommGroupCat.{u}) : Limits.LimitCone (pair G H) where
  cone :=
    { pt := AddCommGroupCat.of (G × H)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (AddMonoidHom.fst G H) (AddMonoidHom.snd G H)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun s => AddMonoidHom.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
      fac := by rintro s (⟨⟩ | ⟨⟩) <;> rfl
      uniq := fun s m w => by
        simp_rw [← w ⟨WalkingPair.left⟩, ← w ⟨WalkingPair.right⟩]
        rfl }
#align AddCommGroup.binary_product_limit_cone AddCommGroupCat.binaryProductLimitCone

@[simp]
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGroupCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = AddMonoidHom.fst G H :=
  rfl
#align AddCommGroup.binary_product_limit_cone_cone_π_app_left AddCommGroupCat.binaryProductLimitCone_cone_π_app_left

@[simp]
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGroupCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = AddMonoidHom.snd G H :=
  rfl
#align AddCommGroup.binary_product_limit_cone_cone_π_app_right AddCommGroupCat.binaryProductLimitCone_cone_π_app_right

/-- We verify that the biproduct in `AddCommGroupCat` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps! hom_apply]
noncomputable def biprodIsoProd (G H : AddCommGroupCat.{u}) :
    (G ⊞ H : AddCommGroupCat) ≅ AddCommGroupCat.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit
#align AddCommGroup.biprod_iso_prod AddCommGroupCat.biprodIsoProd

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGroupCat.biprodIsoProd_hom_apply

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGroupCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = AddMonoidHom.fst G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)
#align AddCommGroup.biprod_iso_prod_inv_comp_fst AddCommGroupCat.biprodIsoProd_inv_comp_fst

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGroupCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = AddMonoidHom.snd G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)
#align AddCommGroup.biprod_iso_prod_inv_comp_snd AddCommGroupCat.biprodIsoProd_inv_comp_snd

namespace HasLimit

variable {J : Type w} (f : J → AddCommGroupCat.{max w u})

/-- The map from an arbitrary cone over an indexed family of abelian groups
to the cartesian product of those groups.
-/
-- This was marked `@[simps]` until we made `AddCommGroupCat.coe_of` a simp lemma,
-- after which the simp normal form linter complains.
-- The generated simp lemmas were not used in Mathlib.
-- Possible solution: higher priority function coercions that remove the `of`?
-- @[simps]
def lift (s : Fan f) : s.pt ⟶ AddCommGroupCat.of (∀ j, f j) where
  toFun x j := s.π.app ⟨j⟩ x
  map_zero' := by
    simp only [Functor.const_obj_obj, map_zero]
    rfl
  map_add' x y := by
    simp only [Functor.const_obj_obj, map_add]
    rfl
#align AddCommGroup.has_limit.lift AddCommGroupCat.HasLimit.lift

/-- Construct limit data for a product in `AddCommGroupCat`, using
`AddCommGroupCat.of (∀ j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := AddCommGroupCat.of (∀ j, f j)
      π := Discrete.natTrans fun j => Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun s j => rfl
      uniq := fun s m w => by
        ext x
        funext j
        exact congr_arg (fun g : s.pt ⟶ f j => (g : s.pt → f j) x) (w ⟨j⟩) }
#align AddCommGroup.has_limit.product_limit_cone AddCommGroupCat.HasLimit.productLimitCone

end HasLimit

open HasLimit

variable {J : Type} [Finite J]

/-- We verify that the biproduct we've just defined is isomorphic to the `AddCommGroupCat` structure
on the dependent function type.
-/
@[simps! hom_apply]
noncomputable def biproductIsoPi (f : J → AddCommGroupCat.{u}) :
    (⨁ f : AddCommGroupCat) ≅ AddCommGroupCat.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit
#align AddCommGroup.biproduct_iso_pi AddCommGroupCat.biproductIsoPi

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGroupCat.biproductIsoPi_hom_apply

@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGroupCat.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)
#align AddCommGroup.biproduct_iso_pi_inv_comp_π AddCommGroupCat.biproductIsoPi_inv_comp_π

end AddCommGroupCat
