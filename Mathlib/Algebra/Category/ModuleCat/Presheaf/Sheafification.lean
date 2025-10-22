/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# The sheafification functor for presheaves of modules

In this file, we construct a functor
`PresheafOfModules.sheafification α : PresheafOfModules R₀ ⥤ SheafOfModules R`
for a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings.
In particular, if `α` is the identity of `R.val`, we obtain the
sheafification functor `PresheafOfModules R.val ⥤ SheafOfModules R`.

-/

universe v v' u u'

open CategoryTheory Category Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.val)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace PresheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings (i.e. `R` identifies to the sheafification of `R₀`), this is
the associated sheaf of modules functor `PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R`. -/
@[simps! -isSimp map]
noncomputable def sheafification : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where
  obj M₀ := sheafify α (CategoryTheory.toSheafify J M₀.presheaf)
  map f := sheafifyMap _ _ _ f
    ((toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat).map f)
      (by apply toSheafify_naturality)
  map_id M₀ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl
  map_comp _ _ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
noncomputable def sheafificationCompToSheaf :
    sheafification.{v} α ⋙ SheafOfModules.toSheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat :=
  Iso.refl _

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
noncomputable def sheafificationCompForgetCompToPresheaf :
    sheafification.{v} α ⋙ SheafOfModules.forget _ ⋙ toPresheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat ⋙ sheafToPresheaf J AddCommGrpCat :=
  Iso.refl _

/-- The bijection between types of morphisms which is part of the adjunction
`sheafificationAdjunction`. -/
noncomputable def sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R} :
    ((sheafification α).obj P ⟶ F) ≃
      (P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) := by
  apply sheafifyHomEquiv

lemma toPresheaf_map_sheafificationHomEquiv_def
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (sheafificationHomEquiv α f) =
      CategoryTheory.toSheafify J P.presheaf ≫ (toPresheaf R.val).map f.val := rfl

lemma toPresheaf_map_sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (sheafificationHomEquiv α f) =
      (sheafificationAdjunction J AddCommGrpCat).homEquiv P.presheaf
        ((SheafOfModules.toSheaf _).obj F) ((SheafOfModules.toSheaf _).map f) := by
  rw [toPresheaf_map_sheafificationHomEquiv_def, Adjunction.homEquiv_unit]
  dsimp

lemma toSheaf_map_sheafificationHomEquiv_symm
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    (SheafOfModules.toSheaf _).map ((sheafificationHomEquiv α).symm g) =
      (((sheafificationAdjunction J AddCommGrpCat).homEquiv
        P.presheaf ((SheafOfModules.toSheaf R).obj F)).symm ((toPresheaf R₀).map g)) := by
  obtain ⟨f, rfl⟩ := (sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  rfl

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings, this is the adjunction
`sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α`. -/
noncomputable def sheafificationAdjunction :
    sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ sheafificationHomEquiv α
      homEquiv_naturality_left_symm := fun {P₀ Q₀ N} f g ↦ by
        apply (SheafOfModules.toSheaf _).map_injective
        rw [Functor.map_comp]
        erw [toSheaf_map_sheafificationHomEquiv_symm,
          toSheaf_map_sheafificationHomEquiv_symm α g]
        rw [Functor.map_comp]
        apply (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).homEquiv_naturality_left_symm
      homEquiv_naturality_right := fun {P₀ M N} f g ↦ by
        apply (toPresheaf _).map_injective
        erw [toPresheaf_map_sheafificationHomEquiv] }

lemma sheafificationAdjunction_homEquiv_apply {P : PresheafOfModules.{v} R₀}
    {F : SheafOfModules.{v} R} (f : (sheafification α).obj P ⟶ F) :
    (sheafificationAdjunction α).homEquiv P F f = sheafificationHomEquiv α f := rfl

@[simp]
lemma toPresheaf_map_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{v} R₀) :
    (toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀) =
      CategoryTheory.toSheafify J M₀.presheaf := rfl

instance : (sheafification.{v} α).IsLeftAdjoint :=
  (sheafificationAdjunction α).isLeftAdjoint

end

section

variable [HasSheafify J AddCommGrpCat.{v}]

noncomputable instance :
    PreservesFiniteLimits (sheafification.{v} α ⋙ SheafOfModules.toSheaf.{v} R) :=
  comp_preservesFiniteLimits (toPresheaf.{v} R₀) (presheafToSheaf J AddCommGrpCat)

instance : (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _).ReflectsIsomorphisms :=
  inferInstanceAs (SheafOfModules.forget.{v} R ⋙ toPresheaf _).ReflectsIsomorphisms

instance : (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_comp (SheafOfModules.toSheaf.{v} R) (sheafToPresheaf J _)

noncomputable instance : ReflectsFiniteLimits (SheafOfModules.toSheaf.{v} R) where
  reflects _ _ _ := inferInstance

noncomputable instance : PreservesFiniteLimits (sheafification.{v} α) :=
  preservesFiniteLimits_of_reflects_of_preserves
    (sheafification.{v} α) (SheafOfModules.toSheaf.{v} R)

end

end PresheafOfModules
