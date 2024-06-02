/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The sheafification functor for presheaves of modules

In this file, we construct a functor
`PresheafOfModules.sheafification α : PresheafOfModules R₀ ⥤ SheafOfModules R`
for a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a preasheaf of rings
and `R` a sheaf of rings.

-/

universe v v' u u'

open CategoryTheory Category

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.val)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasWeakSheafify J AddCommGroupCat.{v}]
  [J.WEqualsLocallyBijective AddCommGroupCat.{v}]

namespace PresheafOfModules

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a preasheaf of rings
and `R` a sheaf of rings (i.e. `R` identifies to the sheafification of `R₀`), this is
the associated sheaf of modules functor `PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R`. -/
@[simps map]
noncomputable def sheafification : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where
  obj M₀ := sheafify α (CategoryTheory.toSheafify J M₀.presheaf)
  map f := sheafifyMap _ _ _ f ((presheafToSheaf J AddCommGroupCat).map f.hom) (by simp)
  map_id M₀ := by
    ext1
    apply (toPresheaf _).map_injective
    simp [toPresheaf, sheafify]
  map_comp _ _ := by
    ext1
    apply (toPresheaf _).map_injective
    simp [toPresheaf, sheafify]

attribute [-simp] sheafification_map

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
noncomputable def sheafificationCompToSheaf :
    sheafification.{v} α ⋙ SheafOfModules.toSheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGroupCat :=
  Iso.refl _

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
noncomputable def sheafificationCompForgetCompToPresheaf :
    sheafification.{v} α ⋙ SheafOfModules.forget _ ⋙ toPresheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGroupCat ⋙ sheafToPresheaf J AddCommGroupCat :=
  Iso.refl _

/-- The bijection between types of morphisms which is part of the adjunction
`sheafificationAdjunction`. -/
noncomputable def sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R} :
    ((sheafification α).obj P ⟶ F) ≃
      (P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) := by
  apply sheafifyHomEquiv

lemma sheafificationHomEquiv_hom
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (sheafificationHomEquiv α f).hom =
      CategoryTheory.toSheafify J P.presheaf ≫ f.val.hom := rfl

lemma toSheaf_map_sheafificationHomEquiv_symm
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    (SheafOfModules.toSheaf _).map ((sheafificationHomEquiv α).symm g) =
      (((sheafificationAdjunction J AddCommGroupCat).homEquiv
        P.presheaf ((SheafOfModules.toSheaf R).obj F)).symm g.hom) := by
  obtain ⟨f, rfl⟩ := (sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGroupCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  rfl

lemma sheafificationHomEquiv_symm_val_hom
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    ((sheafificationHomEquiv α).symm g).val.hom =
      (((sheafificationAdjunction J AddCommGroupCat).homEquiv
        P.presheaf ((SheafOfModules.toSheaf R).obj F)).symm g.hom).val :=
  (sheafToPresheaf _ _).congr_map (toSheaf_map_sheafificationHomEquiv_symm α g)

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a preasheaf of rings
and `R` a sheaf of rings, this is the adjunction
`sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α`. -/
noncomputable def sheafificationAdjunction :
    sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ sheafificationHomEquiv α
      homEquiv_naturality_left_symm := fun {P₀ Q₀ N} f g ↦ by
        dsimp
        apply (sheafificationHomEquiv α).injective
        erw [Equiv.apply_symm_apply]
        apply (toPresheaf _).map_injective
        dsimp [toPresheaf]
        erw [sheafificationHomEquiv_hom]
        dsimp
        rw [sheafification_map]
        erw [sheafificationHomEquiv_symm_val_hom]
        dsimp
        let adj := CategoryTheory.sheafificationAdjunction J AddCommGroupCat
        change _ = adj.unit.app P₀.presheaf ≫
          (sheafToPresheaf _ _).map ((presheafToSheaf J _).map f.hom ≫
            (adj.homEquiv Q₀.presheaf ((SheafOfModules.toSheaf R).obj N)).symm g.hom)
        rw [← Adjunction.homEquiv_naturality_left_symm, adj.homEquiv_counit]
        erw [← NatTrans.naturality_assoc, adj.right_triangle_components, comp_id]
        rfl
      homEquiv_naturality_right := fun {P₀ M N} f g ↦ by
        apply (toPresheaf _).map_injective
        dsimp [toPresheaf]
        erw [sheafificationHomEquiv_hom, sheafificationHomEquiv_hom]
        simp [restrictScalars] }

instance : (sheafification.{v} α).IsLeftAdjoint :=
  (sheafificationAdjunction α).isLeftAdjoint

end PresheafOfModules
