/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Order.CompletePartialOrder

/-!
# Inverse and direct images of sheaves

The inverse image is constructed using left Kan extension and sheafification.
-/

@[expose] public section

universe w

noncomputable section

open CategoryTheory.Functor

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type*) [Category A] [HasWeakSheafify K A]
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [∀ (G : Cᵒᵖ ⥤ A), F.op.HasLeftKanExtension G]

/-- The inverse image of sheaves along a continuous functor. -/
abbrev inverseImage : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ F.op.lan ⋙ presheafToSheaf K A

/-- Left Kan extension followed by sheafification is left adjoint to direct image. -/
def inverseDirectImageAdjunction :
    inverseImage J K A F ⊣ F.sheafPushforwardContinuous A J K :=
  ((F.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

@[simp]
lemma inverseDirectImageAdjunction_unit_app_val (X : Sheaf J A) :
    ((inverseDirectImageAdjunction J K A F).unit.app X).hom =
    F.op.lanUnit.app X.obj ≫ whiskerLeft F.op (toSheafify K (F.op.lan.obj X.obj)) := by
  change ((sheafToPresheaf J A).map ((inverseDirectImageAdjunction J K A F).unit.app X)) = _
  simp [inverseDirectImageAdjunction, -ObjectProperty.ι_map]

lemma inverseDirectImageAdjunction_unit_app_val_app (X : Sheaf J A) (Y : C) :
    ((inverseDirectImageAdjunction J K A F).unit.app X).hom.app ⟨Y⟩ =
    (F.op.lanUnit.app X.obj).app ⟨Y⟩ ≫ (toSheafify K (F.op.lan.obj X.obj)).app ⟨F.obj Y⟩ := by
  simp

@[simp]
lemma inverseDirectImageAdjunction_counit_app (X : Sheaf K A) :
    ((inverseDirectImageAdjunction J K A F).counit.app X) =
    (presheafToSheaf K A).map ((F.op.lanAdjunction A).counit.app X.obj) ≫
      (sheafificationAdjunction K A).counit.app X := by
  change (𝟭 (Sheaf K A)).map ((inverseDirectImageAdjunction J K A F).counit.app X) = _
  simp [inverseDirectImageAdjunction, -Functor.id_map]

/-- The trivial topology on the category with one object and one morphism. -/
abbrev pointTopology : GrothendieckTopology PUnit := ⊥

/-- Presheaves on the point are equivalent to their category of values. -/
def equivPresheafUnderlying : PUnitᵒᵖ ⥤ A ≌ A where
  functor := {
    obj := fun F ↦ F.obj ⟨PUnit.unit⟩
    map := fun f ↦ f.app _ }
  inverse := Functor.const _
  unitIso := by
    refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun ⟨⟨⟩⟩ ↦ Iso.refl _) ?_) ?_
    · intro ⟨⟨⟩⟩ ⟨⟨⟩⟩ _
      simp [← Functor.map_id]
      rfl
    · aesop
  counitIso := Iso.refl _

/-- Every presheaf on the point with the trivial topology is a sheaf. -/
def equivSheafPresheaf : Sheaf pointTopology A ≌ PUnitᵒᵖ ⥤ A where
  functor := sheafToPresheaf _ _
  inverse := {
    obj := fun F ↦ ⟨F, fun _ ↦ Presieve.isSheaf_bot⟩
    map := fun f ↦ ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory

namespace CategoryTheory.Sheaf

open Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (t : C)
  (A : Type*) [Category A] [HasWeakSheafify J A]

variable [∀ (G : PUnit.{w + 1}ᵒᵖ ⥤ A), ((Functor.const _).obj t).op.HasLeftKanExtension G]

instance : ((Functor.const _).obj t).IsContinuous pointTopology J where
  op_comp_isSheaf_of_types _ := by exact Presieve.isSheaf_bot

/-- Pullback to the point evaluates a sheaf at the chosen object. -/
def pushforwardPointIsoSections : ((Functor.const _).obj t).sheafPushforwardContinuous A
  pointTopology J ⋙
    (equivSheafPresheaf A).functor ⋙ (equivPresheafUnderlying A).functor ≅
    (sheafSections J A).obj ⟨t⟩ := Iso.refl _

end CategoryTheory.Sheaf
