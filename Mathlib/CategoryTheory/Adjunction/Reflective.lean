/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.EpiMono

#align_import category_theory.adjunction.reflective from "leanprover-community/mathlib"@"239d882c4fb58361ee8b3b39fb2091320edef10a"

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`CategoryTheory.Monad.Limits`.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class Reflective (R : D ⥤ C) extends IsRightAdjoint R, Full R, Faithful R
#align category_theory.reflective CategoryTheory.Reflective

variable {i : D ⥤ C}

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/-- For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (ofRightAdjoint i).unit.app (i.obj ((leftAdjoint i).obj X)) =
      i.map ((leftAdjoint i).map ((ofRightAdjoint i).unit.app X)) := by
  rw [← cancel_mono (i.map ((ofRightAdjoint i).counit.app ((leftAdjoint i).obj X))), ←
    i.map_comp]
  simp
#align category_theory.unit_obj_eq_map_unit CategoryTheory.unit_obj_eq_map_unit

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`Functor.essImage.unit_isIso`.
-/
instance isIso_unit_obj [Reflective i] {B : D} : IsIso ((ofRightAdjoint i).unit.app (i.obj B)) := by
  have : (ofRightAdjoint i).unit.app (i.obj B) = inv (i.map ((ofRightAdjoint i).counit.app B)) := by
    rw [← comp_hom_eq_id]
    apply (ofRightAdjoint i).right_triangle_components
  rw [this]
  exact IsIso.inv_isIso
#align category_theory.is_iso_unit_obj CategoryTheory.isIso_unit_obj

/-- If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
theorem Functor.essImage.unit_isIso [Reflective i] {A : C} (h : A ∈ i.essImage) :
    IsIso ((ofRightAdjoint i).unit.app A) := by
  suffices (ofRightAdjoint i).unit.app A = h.getIso.inv ≫
      (ofRightAdjoint i).unit.app (i.obj (Functor.essImage.witness h)) ≫
      (leftAdjoint i ⋙ i).map h.getIso.hom by
    rw [this]
    infer_instance
  rw [← NatTrans.naturality]
  simp
#align category_theory.functor.ess_image.unit_is_iso CategoryTheory.Functor.essImage.unit_isIso

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
theorem mem_essImage_of_unit_isIso [IsRightAdjoint i] (A : C)
    [IsIso ((ofRightAdjoint i).unit.app A)] : A ∈ i.essImage :=
  ⟨(leftAdjoint i).obj A, ⟨(asIso ((ofRightAdjoint i).unit.app A)).symm⟩⟩
#align category_theory.mem_ess_image_of_unit_is_iso CategoryTheory.mem_essImage_of_unit_isIso

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
theorem mem_essImage_of_unit_isSplitMono [Reflective i] {A : C}
    [IsSplitMono ((ofRightAdjoint i).unit.app A)] : A ∈ i.essImage := by
  let η : 𝟭 C ⟶ leftAdjoint i ⋙ i := (ofRightAdjoint i).unit
  haveI : IsIso (η.app (i.obj ((leftAdjoint i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((leftAdjoint i).obj A)))
  haveI := isIso_of_epi_of_isSplitMono (η.app A)
  exact mem_essImage_of_unit_isIso A
#align category_theory.mem_ess_image_of_unit_is_split_mono CategoryTheory.mem_essImage_of_unit_isSplitMono

/-- Composition of reflective functors. -/
instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Reflective F] [Reflective G] :
    Reflective (F ⋙ G) where toFaithful := Faithful.comp F G
#align category_theory.reflective.comp CategoryTheory.Reflective.comp

/-- (Implementation) Auxiliary definition for `unitCompPartialBijective`. -/
def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((leftAdjoint i).obj A) ⟶ i.obj B) :=
  ((Adjunction.ofRightAdjoint i).homEquiv _ _).symm.trans (equivOfFullyFaithful i)
#align category_theory.unit_comp_partial_bijective_aux CategoryTheory.unitCompPartialBijectiveAux

/-- The description of the inverse of the bijection `unitCompPartialBijectiveAux`. -/
theorem unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((leftAdjoint i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (ofRightAdjoint i).unit.app A ≫ f := by
  simp [unitCompPartialBijectiveAux]
#align category_theory.unit_comp_partial_bijective_aux_symm_apply CategoryTheory.unitCompPartialBijectiveAux_symm_apply

/-- If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` given by
precomposing with `η.app A` is a bijection provided `B` is in the essential image of `i`.
That is, the function `fun (f : i.obj (L.obj A) ⟶ B) ↦ η.app A ≫ f` is bijective,
as long as `B` is in the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be described
nicely is shown in `unitCompPartialBijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`. In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the same: specifically
that `η.app A` is an isomorphism.
-/
def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : B ∈ i.essImage) :
    (A ⟶ B) ≃ (i.obj ((leftAdjoint i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((leftAdjoint i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)
#align category_theory.unit_comp_partial_bijective CategoryTheory.unitCompPartialBijective

@[simp]
theorem unitCompPartialBijective_symm_apply [Reflective i] (A : C) {B : C} (hB : B ∈ i.essImage)
    (f) : (unitCompPartialBijective A hB).symm f = (ofRightAdjoint i).unit.app A ≫ f := by
  simp [unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply]
#align category_theory.unit_comp_partial_bijective_symm_apply CategoryTheory.unitCompPartialBijective_symm_apply

theorem unitCompPartialBijective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : B ∈ i.essImage) (hB' : B' ∈ i.essImage) (f : i.obj ((leftAdjoint i).obj A) ⟶ B) :
    (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBijective A hB).symm f ≫ h := by
  simp
#align category_theory.unit_comp_partial_bijective_symm_natural CategoryTheory.unitCompPartialBijective_symm_natural

theorem unitCompPartialBijective_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : B ∈ i.essImage) (hB' : B' ∈ i.essImage) (f : A ⟶ B) :
    (unitCompPartialBijective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h := by
  rw [← Equiv.eq_symm_apply, unitCompPartialBijective_symm_natural A h, Equiv.symm_apply_apply]
#align category_theory.unit_comp_partial_bijective_natural CategoryTheory.unitCompPartialBijective_natural

instance [Reflective i] (X : Functor.EssImageSubcategory i) :
  IsIso (NatTrans.app (ofRightAdjoint i).unit X.obj) :=
Functor.essImage.unit_isIso X.property

-- Porting note: the following auxiliary definition and the next two lemmas were
-- introduced in order to ease the port
/-- The counit isomorphism of the equivalence `D ≌ i.EssImageSubcategory` given
by `equivEssImageOfReflective` when the functor `i` is reflective. -/
def equivEssImageOfReflective_counitIso_app [Reflective i] (X : Functor.EssImageSubcategory i) :
    ((Functor.essImageInclusion i ⋙ leftAdjoint i) ⋙ Functor.toEssImage i).obj X ≅ X := by
  refine' Iso.symm (@asIso _ _ X _ ((ofRightAdjoint i).unit.app X.obj) ?_)
  refine @isIso_of_reflects_iso _ _ _ _ _ _ _ i.essImageInclusion ?_ _
  dsimp
  exact inferInstance

lemma equivEssImageOfReflective_map_counitIso_app_hom [Reflective i]
    (X : Functor.EssImageSubcategory i) :
  (Functor.essImageInclusion i).map (equivEssImageOfReflective_counitIso_app X).hom =
    inv (NatTrans.app (ofRightAdjoint i).unit X.obj) := by
    simp only [Functor.comp_obj, Functor.essImageInclusion_obj, Functor.toEssImage_obj_obj,
      equivEssImageOfReflective_counitIso_app, asIso, Iso.symm_mk, Functor.essImageInclusion_map,
      Functor.id_obj]
    rfl

lemma equivEssImageOfReflective_map_counitIso_app_inv [Reflective i]
    (X : Functor.EssImageSubcategory i) :
  (Functor.essImageInclusion i).map (equivEssImageOfReflective_counitIso_app X).inv =
    (NatTrans.app (ofRightAdjoint i).unit X.obj) := rfl

/-- If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.essImage` can be explicitly
defined by the reflector. -/
@[simps]
def equivEssImageOfReflective [Reflective i] : D ≌ i.EssImageSubcategory
    where
  functor := i.toEssImage
  inverse := i.essImageInclusion ⋙ (leftAdjoint i : _)
  unitIso :=
    NatIso.ofComponents (fun X => (asIso <| (ofRightAdjoint i).counit.app X).symm)
      (by
        intro X Y f
        dsimp
        rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
        exact ((ofRightAdjoint i).counit.naturality f).symm)
  counitIso :=
    NatIso.ofComponents equivEssImageOfReflective_counitIso_app
      (by
        intro X Y f
        apply (Functor.essImageInclusion i).map_injective
        have h := ((ofRightAdjoint i).unit.naturality f).symm
        rw [Functor.id_map] at h
        erw [Functor.map_comp, Functor.map_comp,
          equivEssImageOfReflective_map_counitIso_app_hom,
          equivEssImageOfReflective_map_counitIso_app_hom,
          IsIso.comp_inv_eq, assoc, ← h, IsIso.inv_hom_id_assoc, Functor.comp_map])
  functor_unitIso_comp := fun X => by
    -- Porting note: this proof was automatically handled by the automation in mathlib
    apply (Functor.essImageInclusion i).map_injective
    erw [Functor.map_comp, equivEssImageOfReflective_map_counitIso_app_hom]
    aesop_cat
#align category_theory.equiv_ess_image_of_reflective CategoryTheory.equivEssImageOfReflective

end CategoryTheory
