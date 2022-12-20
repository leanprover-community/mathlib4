/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.essential_image
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Essential image of a functor

The essential image `ess_image` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into a essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D}

namespace Functor

/-- The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def essImage (F : C ⥤ D) : Set D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)
#align category_theory.functor.ess_image CategoryTheory.Functor.essImage

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def essImage.witness {Y : D} (h : Y ∈ F.essImage) : C :=
  h.some
#align category_theory.functor.ess_image.witness CategoryTheory.Functor.essImage.witness

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def essImage.getIso {Y : D} (h : Y ∈ F.essImage) : F.obj h.witness ≅ Y :=
  Classical.choice h.some_spec
#align category_theory.functor.ess_image.get_iso CategoryTheory.Functor.essImage.getIso

/-- Being in the essential image is a "hygenic" property: it is preserved under isomorphism. -/
theorem essImage.of_iso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ essImage F) : Y' ∈ essImage F :=
  hY.imp fun B => Nonempty.map (· ≪≫ h)
#align category_theory.functor.ess_image.of_iso CategoryTheory.Functor.essImage.of_iso

/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem essImage.of_nat_iso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ essImage F) :
    Y ∈ essImage F' :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t
#align category_theory.functor.ess_image.of_nat_iso CategoryTheory.Functor.essImage.of_nat_iso

/-- Isomorphic functors have equal essential images. -/
theorem ess_image_eq_of_nat_iso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.of_nat_iso h, essImage.of_nat_iso h.symm⟩
#align
  category_theory.functor.ess_image_eq_of_nat_iso CategoryTheory.Functor.ess_image_eq_of_nat_iso

/-- An object in the image is in the essential image. -/
theorem obj_mem_ess_image (F : D ⥤ C) (Y : D) : F.obj Y ∈ essImage F :=
  ⟨Y, ⟨Iso.refl _⟩⟩
#align category_theory.functor.obj_mem_ess_image CategoryTheory.Functor.obj_mem_ess_image

/-- The essential image of a functor, interpreted of a full subcategory of the target category. -/
@[nolint has_nonempty_instance]
def EssImageSubcategory (F : C ⥤ D) :=
  FullSubcategory F.essImage deriving Category
#align category_theory.functor.ess_image_subcategory CategoryTheory.Functor.EssImageSubcategory

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps]
def essImageInclusion (F : C ⥤ D) : F.EssImageSubcategory ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align category_theory.functor.ess_image_inclusion CategoryTheory.Functor.essImageInclusion

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps]
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  FullSubcategory.lift _ F (obj_mem_ess_image _)
#align category_theory.functor.to_ess_image CategoryTheory.Functor.toEssImage

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps]
def toEssImageCompEssentialImageInclusion (F : C ⥤ D) : F.toEssImage ⋙ F.essImageInclusion ≅ F :=
  FullSubcategory.liftCompInclusion _ _ _
#align
  category_theory.functor.to_ess_image_comp_essential_image_inclusion CategoryTheory.Functor.toEssImageCompEssentialImageInclusion

end Functor

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`mem_ess_image] [] -/
/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class EssSurj (F : C ⥤ D) : Prop where
  mem_ess_image (Y : D) : Y ∈ F.essImage
#align category_theory.ess_surj CategoryTheory.EssSurj

instance :
    EssSurj
      F.toEssImage where mem_ess_image := fun ⟨Y, hY⟩ =>
    ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

variable (F) [EssSurj F]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def Functor.objPreimage (Y : D) : C :=
  (EssSurj.mem_ess_image F Y).witness
#align category_theory.functor.obj_preimage CategoryTheory.Functor.objPreimage

/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def Functor.objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  (EssSurj.mem_ess_image F Y).getIso
#align category_theory.functor.obj_obj_preimage_iso CategoryTheory.Functor.objObjPreimageIso

/-- The induced functor of a faithful functor is faithful -/
instance Faithful.to_ess_image (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage :=
  Faithful.of_comp_iso F.toEssImageCompEssentialImageInclusion
#align category_theory.faithful.to_ess_image CategoryTheory.Faithful.to_ess_image

/-- The induced functor of a full functor is full -/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage :=
  haveI := full.of_iso F.to_ess_image_comp_essential_image_inclusion.symm
  full.of_comp_faithful F.to_ess_image F.ess_image_inclusion
#align category_theory.full.to_ess_image CategoryTheory.Full.toEssImage

end CategoryTheory

