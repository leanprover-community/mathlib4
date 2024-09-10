/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# The category of abelian groups has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

universe w u

namespace AddCommGrp

-- As `AddCommGrp` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts AddCommGrp :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts AddCommGrp :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `AddCommGrp`, using
`AddCommGrp.of (G × H)`.
-/
@[simps cone_pt isLimit_lift]
def binaryProductLimitCone (G H : AddCommGrp.{u}) : Limits.LimitCone (pair G H) where
  cone :=
    { pt := AddCommGrp.of (G × H)
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

@[simp]
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGrp.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = AddMonoidHom.fst G H :=
  rfl

@[simp]
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGrp.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = AddMonoidHom.snd G H :=
  rfl

/-- We verify that the biproduct in `AddCommGrp` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps! hom_apply]
noncomputable def biprodIsoProd (G H : AddCommGrp.{u}) :
    (G ⊞ H : AddCommGrp) ≅ AddCommGrp.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGrp.biprodIsoProd_hom_apply

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrp.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = AddMonoidHom.fst G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrp.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = AddMonoidHom.snd G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

namespace HasLimit

variable {J : Type w} (f : J → AddCommGrp.{max w u})

/-- The map from an arbitrary cone over an indexed family of abelian groups
to the cartesian product of those groups.
-/
-- This was marked `@[simps]` until we made `AddCommGrp.coe_of` a simp lemma,
-- after which the simp normal form linter complains.
-- The generated simp lemmas were not used in Mathlib.
-- Possible solution: higher priority function coercions that remove the `of`?
-- @[simps]
def lift (s : Fan f) : s.pt ⟶ AddCommGrp.of (∀ j, f j) where
  toFun x j := s.π.app ⟨j⟩ x
  map_zero' := by
    simp only [Functor.const_obj_obj, map_zero]
    rfl
  map_add' x y := by
    simp only [Functor.const_obj_obj, map_add]
    rfl

/-- Construct limit data for a product in `AddCommGrp`, using
`AddCommGrp.of (∀ j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := AddCommGrp.of (∀ j, f j)
      π := Discrete.natTrans fun j => Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun s j => rfl
      uniq := fun s m w => by
        ext x
        funext j
        exact congr_arg (fun g : s.pt ⟶ f j => (g : s.pt → f j) x) (w ⟨j⟩) }

end HasLimit

open HasLimit

variable {J : Type} [Finite J]

/-- We verify that the biproduct we've just defined is isomorphic to the `AddCommGrp` structure
on the dependent function type.
-/
@[simps! hom_apply]
noncomputable def biproductIsoPi (f : J → AddCommGrp.{u}) :
    (⨁ f : AddCommGrp) ≅ AddCommGrp.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGrp.biproductIsoPi_hom_apply

@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGrp.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end AddCommGrp
