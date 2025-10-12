/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
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

namespace AddCommGrpCat

-- As `AddCommGrpCat` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts AddCommGrpCat :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts AddCommGrpCat :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `AddCommGrpCat`, using
`AddCommGrpCat.of (G × H)`.
-/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : AddCommGrpCat.{u}) : Limits.LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

@[simp]
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGrpCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = ofHom (AddMonoidHom.fst G H) :=
  rfl

@[simp]
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGrpCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = ofHom (AddMonoidHom.snd G H) :=
  rfl

/-- We verify that the biproduct in `AddCommGrpCat` is isomorphic to
the Cartesian product of the underlying types:
-/
noncomputable def biprodIsoProd (G H : AddCommGrpCat.{u}) :
    (G ⊞ H : AddCommGrpCat) ≅ AddCommGrpCat.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrpCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = ofHom (AddMonoidHom.fst G H) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrpCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = ofHom (AddMonoidHom.snd G H) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

namespace HasLimit

variable {J : Type w} (f : J → AddCommGrpCat.{max w u})

/-- The map from an arbitrary cone over an indexed family of abelian groups
to the Cartesian product of those groups.
-/
@[simps!]
def lift (s : Fan f) : s.pt ⟶ AddCommGrpCat.of (∀ j, f j) :=
  ofHom
  { toFun x j := s.π.app ⟨j⟩ x
    map_zero' := by
      simp only [Functor.const_obj_obj, map_zero]
      rfl
    map_add' x y := by
      simp only [Functor.const_obj_obj, map_add]
      rfl }

/-- Construct limit data for a product in `AddCommGrpCat`, using
`AddCommGrpCat.of (∀ j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := AddCommGrpCat.of (∀ j, f j)
      π := Discrete.natTrans fun j => ofHom <| Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact CategoryTheory.congr_fun (w ⟨j⟩) x }

end HasLimit

open HasLimit

variable {J : Type} [Finite J]

/-- We verify that the biproduct we've just defined is isomorphic to the `AddCommGrpCat` structure
on the dependent function type.
-/
noncomputable def biproductIsoPi (f : J → AddCommGrpCat.{u}) :
    (⨁ f : AddCommGrpCat) ≅ AddCommGrpCat.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGrpCat.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (Pi.evalAddMonoidHom (fun j => f j) j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end AddCommGrpCat
