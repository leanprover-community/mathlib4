/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Properties of objects in comma categories

-/

universe w

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  (F₁ : C₁ ⥤ D) (F₂ : C₂ ⥤ D)
  (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂)

/-- Given functors `F₁ : C₁ ⥤ D` and `F₂ : C₂ ⥤ D`, and properties
of objects `P₁ : ObjectProperty C₁` and `P₂ : ObjectProperty C₂`,
this is the property of objects in `Comma F₁ F₂` satisfying
by the objects corresponding to morphisms `F₁.obj X₁ ⟶ F₂.obj X₂`
where `P₁ X₁` and `P₂ X₂` hold. -/
def comma : ObjectProperty (Comma F₁ F₂) :=
  P₁.inverseImage (Comma.fst _ _) ⊓ P₂.inverseImage (Comma.snd _ _)

variable {F₁ F₂} in
@[simp]
lemma comma_iff (X : Comma F₁ F₂) :
    comma F₁ F₂ P₁ P₂ X ↔ P₁ X.left ∧ P₂ X.right := Iff.rfl

instance [P₁.IsStableUnderRetracts] [P₂.IsStableUnderRetracts] :
    (comma F₁ F₂ P₁ P₂).IsStableUnderRetracts where
  of_retract r h :=
    ⟨P₁.prop_of_retract (r.map (Comma.fst _ _)) h.1,
      P₂.prop_of_retract (r.map (Comma.snd _ _)) h.2⟩

instance [P₁.IsClosedUnderIsomorphisms] [P₂.IsClosedUnderIsomorphisms] :
    (comma F₁ F₂ P₁ P₂).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨P₁.prop_of_iso ((Comma.fst _ _).mapIso e) h.1,
      P₂.prop_of_iso ((Comma.snd _ _).mapIso e) h.2⟩

instance [ObjectProperty.Small.{w} P₁] [ObjectProperty.Small.{w} P₂] [LocallySmall.{w} D] :
    ObjectProperty.Small.{w} (comma F₁ F₂ P₁ P₂) :=
  small_of_surjective
    (α := Σ (X₁ : Subtype P₁) (X₂ : Subtype P₂), F₁.obj X₁.val ⟶ F₂.obj X₂.val)
    (f := fun ⟨X₁, X₂, f⟩ ↦ ⟨Comma.mk _ _ f, X₁.prop, X₂.prop⟩)
    (fun f ↦ ⟨⟨⟨_, f.prop.1⟩, ⟨_, f.prop.2⟩, f.val.hom⟩, rfl⟩)

instance [ObjectProperty.EssentiallySmall.{w} P₁]
    [ObjectProperty.EssentiallySmall.{w} P₂] [LocallySmall.{w} D] :
    ObjectProperty.EssentiallySmall.{w} (comma F₁ F₂ P₁ P₂) := by
  obtain ⟨Q₁, _, h₁, h₁'⟩ := EssentiallySmall.exists_small_le.{w} P₁
  obtain ⟨Q₂, _, h₂, h₂'⟩ := EssentiallySmall.exists_small_le.{w} P₂
  refine ⟨comma F₁ F₂ Q₁ Q₂, inferInstance, fun f hf ↦ ?_⟩
  simp only [comma_iff] at hf
  obtain ⟨X₁, hX₁, ⟨e₁⟩⟩ := h₁' _ hf.1
  obtain ⟨X₂, hX₂, ⟨e₂⟩⟩ := h₂' _ hf.2
  exact ⟨Comma.mk _ _ (F₁.map e₁.inv ≫ f.hom ≫ F₂.map e₂.hom), by tauto,
    ⟨Comma.isoMk e₁ e₂⟩⟩

end CategoryTheory.ObjectProperty
