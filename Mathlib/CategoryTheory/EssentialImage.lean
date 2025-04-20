/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

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
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}

namespace Functor

/-- The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def essImage (F : C ⥤ D) : ObjectProperty D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def essImage.witness {Y : D} (h : F.essImage Y) : C :=
  h.choose

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def essImage.getIso {Y : D} (h : F.essImage Y) : F.obj h.witness ≅ Y :=
  Classical.choice h.choose_spec

/-- Being in the essential image is a "hygienic" property: it is preserved under isomorphism. -/
theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : essImage F Y) : essImage F Y' :=
  hY.imp fun _ => Nonempty.map (· ≪≫ h)

instance : F.essImage.IsClosedUnderIsomorphisms where
  of_iso e h := essImage.ofIso e h

/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : essImage F Y) :
    essImage F' Y :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

/-- Isomorphic functors have equal essential images. -/
theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

/-- An object in the image is in the essential image. -/
theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : essImage F (F.obj Y) :=
  ⟨Y, ⟨Iso.refl _⟩⟩

/-- The essential image of a functor, interpreted as a full subcategory of the target category. -/
def EssImageSubcategory (F : C ⥤ D) :=
  FullSubcategory F.essImage
-- The `Category` instance should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance : Category (EssImageSubcategory F) :=
  (inferInstance : Category.{v₂} (FullSubcategory _))

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps!]
def essImageInclusion (F : C ⥤ D) : F.EssImageSubcategory ⥤ D :=
  fullSubcategoryInclusion _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance : Full (essImageInclusion F) :=
  (inferInstance : Full (fullSubcategoryInclusion _))

instance : Faithful (essImageInclusion F) :=
  (inferInstance : Faithful (fullSubcategoryInclusion _))

lemma essImage_ext (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
    (h : F.essImageInclusion.map f = F.essImageInclusion.map g) : f = g := by
  simpa using h

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps!]
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  FullSubcategory.lift _ F (obj_mem_essImage _)

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps!]
def toEssImageCompEssentialImageInclusion (F : C ⥤ D) : F.toEssImage ⋙ F.essImageInclusion ≅ F :=
  FullSubcategory.lift_comp_inclusion _ _ _

/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential
image of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`. -/
@[stacks 001C]
class EssSurj (F : C ⥤ D) : Prop where
  /-- All the objects of the target category are in the essential image. -/
  mem_essImage (Y : D) : F.essImage Y

instance EssSurj.toEssImage : EssSurj F.toEssImage where
  mem_essImage := fun ⟨_, hY⟩ =>
    ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

theorem essSurj_of_surj (h : Function.Surjective F.obj) : EssSurj F where
  mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

section EssSurj
variable (F)
variable [F.EssSurj]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def objPreimage (Y : D) : C :=
  essImage.witness (@EssSurj.mem_essImage _ _ _ _ F _ Y)

/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  Functor.essImage.getIso _

/-- The induced functor of a faithful functor is faithful. -/
instance Faithful.toEssImage (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage :=
  Faithful.of_comp_iso F.toEssImageCompEssentialImageInclusion

/-- The induced functor of a full functor is full. -/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage :=
  Full.of_comp_faithful_iso F.toEssImageCompEssentialImageInclusion

instance instEssSurjId : EssSurj (𝟭 C) where
  mem_essImage Y := ⟨Y, ⟨Iso.refl _⟩⟩

lemma essSurj_of_iso {F G : C ⥤ D} [EssSurj F] (α : F ≅ G) : EssSurj G where
  mem_essImage Y := Functor.essImage.ofNatIso α (EssSurj.mem_essImage Y)

instance essSurj_comp (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F ⋙ G).EssSurj where
  mem_essImage Z := ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩

lemma essSurj_of_comp_fully_faithful (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj]
    [G.Faithful] [G.Full] : F.EssSurj where
  mem_essImage X := ⟨_, ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj X))⟩⟩

variable {F} {X : E}

/-- Pre-composing by an essentially surjective functor doesn't change the essential image. -/
lemma essImage_comp_apply_of_essSurj : (F ⋙ G).essImage X ↔ G.essImage X where
  mp := fun ⟨Y, ⟨e⟩⟩ ↦ ⟨F.obj Y, ⟨e⟩⟩
  mpr := fun ⟨Y, ⟨e⟩⟩ ↦
    let ⟨Z, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage Y; ⟨Z, ⟨(G.mapIso e').trans e⟩⟩

/-- Pre-composing by an essentially surjective functor doesn't change the essential image. -/
@[simp] lemma essImage_comp_of_essSurj : (F ⋙ G).essImage = G.essImage :=
  funext fun _X ↦ propext essImage_comp_apply_of_essSurj

end EssSurj

variable {J C D : Type*} [Category J] [Category C] [Category D]
  (G : J ⥤ D) (F : C ⥤ D) [F.Full] [F.Faithful] (hG : ∀ j, F.essImage (G.obj j))

/-- Lift a functor `G : J ⥤ D` to the essential image of a fully functor `F : C ⥤ D` to a functor
`G' : J ⥤ C` such that `G' ⋙ F ≅ G`. See `essImage.liftFunctorCompIso`. -/
@[simps] def essImage.liftFunctor : J ⥤ C where
  obj j := F.toEssImage.objPreimage ⟨G.obj j, hG j⟩
  -- TODO: `map` isn't type-correct:
  -- It conflates `⟨G.obj i, hG i⟩ ⟶ ⟨G.obj j, hG j⟩` and `G.obj i ⟶ G.obj j`.
  map {i j} f := F.preimage <|
    (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG i⟩).hom ≫ G.map f ≫
      (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv
  map_id i := F.map_injective <| by
    simpa [-Iso.hom_inv_id] using (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG i⟩).hom_inv_id
  map_comp {i j k} f g := F.map_injective <| by
    simp only [Functor.map_comp, Category.assoc, Functor.map_preimage]
    congr 2
    symm
    convert (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv_hom_id_assoc (G.map g ≫
      (F.toEssImage.objObjPreimageIso ⟨G.obj k, hG k⟩).inv)

/-- A functor `G : J ⥤ D` to the essential image of a fully functor `F : C ⥤ D` does factor through
`essImage.liftFunctor G F hG`. -/
@[simps!] def essImage.liftFunctorCompIso : essImage.liftFunctor G F hG ⋙ F ≅ G :=
  NatIso.ofComponents
    (fun i ↦ F.essImageInclusion.mapIso (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG _⟩))
      fun {i j} f ↦ by
    simp only [Functor.comp_obj, liftFunctor_obj, Functor.comp_map, liftFunctor_map,
      Functor.map_preimage, Functor.mapIso_hom, Functor.essImageInclusion_map, Category.assoc]
    congr 1
    convert Category.comp_id _
    exact (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv_hom_id

end Functor

end CategoryTheory
