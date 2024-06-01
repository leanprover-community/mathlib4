/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.FullSubcategory

#align_import category_theory.essential_image from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

/-!
# Essential image of a functor

The essential image `essImage` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into an essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D}

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
  h.choose
#align category_theory.functor.ess_image.witness CategoryTheory.Functor.essImage.witness

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
-- Porting note: in the next, the dot notation `h.witness` no longer works
def essImage.getIso {Y : D} (h : Y ∈ F.essImage) : F.obj (essImage.witness h) ≅ Y :=
  Classical.choice h.choose_spec
#align category_theory.functor.ess_image.get_iso CategoryTheory.Functor.essImage.getIso

/-- Being in the essential image is a "hygienic" property: it is preserved under isomorphism. -/
theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ essImage F) : Y' ∈ essImage F :=
  hY.imp fun _ => Nonempty.map (· ≪≫ h)
#align category_theory.functor.ess_image.of_iso CategoryTheory.Functor.essImage.ofIso

/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ essImage F) :
    Y ∈ essImage F' :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t
#align category_theory.functor.ess_image.of_nat_iso CategoryTheory.Functor.essImage.ofNatIso

/-- Isomorphic functors have equal essential images. -/
theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩
#align category_theory.functor.ess_image_eq_of_nat_iso CategoryTheory.Functor.essImage_eq_of_natIso

/-- An object in the image is in the essential image. -/
theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : F.obj Y ∈ essImage F :=
  ⟨Y, ⟨Iso.refl _⟩⟩
#align category_theory.functor.obj_mem_ess_image CategoryTheory.Functor.obj_mem_essImage

/-- The essential image of a functor, interpreted as a full subcategory of the target category. -/
-- Porting note: no hasNonEmptyInstance linter yet
def EssImageSubcategory (F : C ⥤ D) :=
  FullSubcategory F.essImage
#align category_theory.functor.ess_image_subcategory CategoryTheory.Functor.EssImageSubcategory

-- Porting note: `deriving Category` is not able to derive this instance
instance : Category (EssImageSubcategory F) :=
  (inferInstance : Category.{v₂} (FullSubcategory _))

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps!]
def essImageInclusion (F : C ⥤ D) : F.EssImageSubcategory ⥤ D :=
  fullSubcategoryInclusion _
#align category_theory.functor.ess_image_inclusion CategoryTheory.Functor.essImageInclusion
#align category_theory.functor.ess_image_inclusion_obj CategoryTheory.Functor.essImageInclusion_obj
#align category_theory.functor.ess_image_inclusion_map CategoryTheory.Functor.essImageInclusion_map

-- Porting note: `deriving Full` is not able to derive this instance
instance : Full (essImageInclusion F) :=
  (inferInstance : Full (fullSubcategoryInclusion _))

-- Porting note: `deriving Faithful` is not able to derive this instance
instance : Faithful (essImageInclusion F) :=
  (inferInstance : Faithful (fullSubcategoryInclusion _))

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps!]
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  FullSubcategory.lift _ F (obj_mem_essImage _)
#align category_theory.functor.to_ess_image CategoryTheory.Functor.toEssImage
#align category_theory.functor.to_ess_image_map CategoryTheory.Functor.toEssImage_map
#align category_theory.functor.to_ess_image_obj_obj CategoryTheory.Functor.toEssImage_obj_obj

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps!]
def toEssImageCompEssentialImageInclusion (F : C ⥤ D) : F.toEssImage ⋙ F.essImageInclusion ≅ F :=
  FullSubcategory.lift_comp_inclusion _ _ _
#align category_theory.functor.to_ess_image_comp_essential_image_inclusion CategoryTheory.Functor.toEssImageCompEssentialImageInclusion
#align category_theory.functor.to_ess_image_comp_essential_image_inclusion_hom_app CategoryTheory.Functor.toEssImageCompEssentialImageInclusion_hom_app
#align category_theory.functor.to_ess_image_comp_essential_image_inclusion_inv_app CategoryTheory.Functor.toEssImageCompEssentialImageInclusion_inv_app

/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential
image of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class EssSurj (F : C ⥤ D) : Prop where
  /-- All the objects of the target category are in the essential image. -/
  mem_essImage (Y : D) : Y ∈ F.essImage
#align category_theory.ess_surj CategoryTheory.Functor.EssSurj

instance EssSurj.toEssImage : EssSurj F.toEssImage where
  mem_essImage := fun ⟨_, hY⟩ =>
    ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

variable (F)
variable [F.EssSurj]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def objPreimage (Y : D) : C :=
  essImage.witness (@EssSurj.mem_essImage _ _ _ _ F _ Y)
#align category_theory.functor.obj_preimage CategoryTheory.Functor.objPreimage

/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  Functor.essImage.getIso _
#align category_theory.functor.obj_obj_preimage_iso CategoryTheory.Functor.objObjPreimageIso

/-- The induced functor of a faithful functor is faithful. -/
instance Faithful.toEssImage (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage :=
  Faithful.of_comp_iso F.toEssImageCompEssentialImageInclusion
#align category_theory.faithful.to_ess_image CategoryTheory.Functor.Faithful.toEssImage

/-- The induced functor of a full functor is full. -/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage :=
  Full.of_comp_faithful_iso F.toEssImageCompEssentialImageInclusion
#align category_theory.full.to_ess_image CategoryTheory.Functor.Full.toEssImage

instance instEssSurjId : EssSurj (𝟭 C) where
  mem_essImage Y := ⟨Y, ⟨Iso.refl _⟩⟩

theorem essSurj_of_surj (h : Function.Surjective F.obj) : EssSurj F where
  mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

lemma essSurj_of_iso {F G : C ⥤ D} [EssSurj F] (α : F ≅ G) : EssSurj G where
  mem_essImage Y := Functor.essImage.ofNatIso α (EssSurj.mem_essImage Y)

instance essSurj_comp (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F ⋙ G).EssSurj where
  mem_essImage Z := ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩

end Functor

-- deprecated on 2024-04-06
@[deprecated] alias EssSurj := Functor.EssSurj
@[deprecated] alias Iso.map_essSurj := Functor.essSurj_of_iso

end CategoryTheory
