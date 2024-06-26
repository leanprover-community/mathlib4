/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Morphism properties that are inverted by a functor

In this file, we introduce the predicate `P.IsInvertedBy F` which expresses
that the morphisms satisfying `P : MorphismProperty C` are mapped to
isomorphisms by a functor `F : C ⥤ D`.

This is used in the localization of categories API (folder `CategoryTheory.Localization`).

-/

universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- If `P : MorphismProperty C` and `F : C ⥤ D`, then
`P.IsInvertedBy F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)
#align category_theory.morphism_property.is_inverted_by CategoryTheory.MorphismProperty.IsInvertedBy

namespace IsInvertedBy

lemma of_le (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P ≤ Q) :
    P.IsInvertedBy F :=
  fun _ _ _ hf => hQ _ (h _ hf)

theorem of_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) :
    W.IsInvertedBy (F ⋙ G) := fun X Y f hf => by
  haveI := hF f hf
  dsimp
  infer_instance
#align category_theory.morphism_property.is_inverted_by.of_comp CategoryTheory.MorphismProperty.IsInvertedBy.of_comp

theorem op {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op :=
  fun X Y f hf => by
  haveI := h f.unop hf
  dsimp
  infer_instance
#align category_theory.morphism_property.is_inverted_by.op CategoryTheory.MorphismProperty.IsInvertedBy.op

theorem rightOp {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.rightOp := fun X Y f hf => by
  haveI := h f.op hf
  dsimp
  infer_instance
#align category_theory.morphism_property.is_inverted_by.right_op CategoryTheory.MorphismProperty.IsInvertedBy.rightOp

theorem leftOp {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L) :
    W.op.IsInvertedBy L.leftOp := fun X Y f hf => by
  haveI := h f.unop hf
  dsimp
  infer_instance
#align category_theory.morphism_property.is_inverted_by.left_op CategoryTheory.MorphismProperty.IsInvertedBy.leftOp

theorem unop {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.unop := fun X Y f hf => by
  haveI := h f.op hf
  dsimp
  infer_instance
#align category_theory.morphism_property.is_inverted_by.unop CategoryTheory.MorphismProperty.IsInvertedBy.unop

lemma prod {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    {E₁ E₂ : Type*} [Category E₁] [Category E₂] {F₁ : C₁ ⥤ E₁} {F₂ : C₂ ⥤ E₂}
    (h₁ : W₁.IsInvertedBy F₁) (h₂ : W₂.IsInvertedBy F₂) :
    (W₁.prod W₂).IsInvertedBy (F₁.prod F₂) := fun _ _ f hf => by
  rw [isIso_prod_iff]
  exact ⟨h₁ _ hf.1, h₂ _ hf.2⟩

lemma pi {J : Type w} {C : J → Type u} {D : J → Type u'}
    [∀ j, Category.{v} (C j)] [∀ j, Category.{v'} (D j)]
    (W : ∀ j, MorphismProperty (C j)) (F : ∀ j, C j ⥤ D j)
    (hF : ∀ j, (W j).IsInvertedBy (F j)) :
    (MorphismProperty.pi W).IsInvertedBy (Functor.pi F) := by
  intro _ _ f hf
  rw [isIso_pi_iff]
  intro j
  exact hF j _ (hf j)

end IsInvertedBy

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- The full subcategory of `C ⥤ D` consisting of functors inverting morphisms in `W` -/
def FunctorsInverting (W : MorphismProperty C) (D : Type*) [Category D] :=
  FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F
#align category_theory.morphism_property.functors_inverting CategoryTheory.MorphismProperty.FunctorsInverting

@[ext]
lemma FunctorsInverting.ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    (h : F₁.obj = F₂.obj) : F₁ = F₂ := by
  cases F₁
  cases F₂
  subst h
  rfl

instance (W : MorphismProperty C) (D : Type*) [Category D] : Category (FunctorsInverting W D) :=
  FullSubcategory.category _

-- Porting note: add another `@[ext]` lemma
-- since `ext` can't see through the definition to use `NatTrans.ext`.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma FunctorsInverting.hom_ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    {α β : F₁ ⟶ F₂} (h : α.app = β.app) : α = β :=
  NatTrans.ext _ _ h

/-- A constructor for `W.FunctorsInverting D` -/
def FunctorsInverting.mk {W : MorphismProperty C} {D : Type*} [Category D] (F : C ⥤ D)
    (hF : W.IsInvertedBy F) : W.FunctorsInverting D :=
  ⟨F, hF⟩
#align category_theory.morphism_property.functors_inverting.mk CategoryTheory.MorphismProperty.FunctorsInverting.mk

theorem IsInvertedBy.iff_of_iso (W : MorphismProperty C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) :
    W.IsInvertedBy F₁ ↔ W.IsInvertedBy F₂ := by
  dsimp [IsInvertedBy]
  simp only [NatIso.isIso_map_iff e]
#align category_theory.morphism_property.is_inverted_by.iff_of_iso CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso

@[simp]
lemma IsInvertedBy.isoClosure_iff (W : MorphismProperty C) (F : C ⥤ D) :
    W.isoClosure.IsInvertedBy F ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    exact h _ (W.le_isoClosure _ hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    have : f = e.inv.left ≫ f' ≫ e.hom.right := by
      erw [← e.hom.w, ← Arrow.comp_left_assoc, e.inv_hom_id, Category.id_comp]
      rfl
    simp only [this, F.map_comp]
    have := h _ hf'
    infer_instance

@[simp]
lemma IsInvertedBy.iff_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [G.ReflectsIsomorphisms] :
    W.IsInvertedBy (F ⋙ G) ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    have : IsIso (G.map (F.map f)) := h _ hf
    exact isIso_of_reflects_iso (F.map f) G
  · intro hF
    exact IsInvertedBy.of_comp W F hF G

lemma IsInvertedBy.iff_le_inverseImage_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W ≤ (isomorphisms D).inverseImage F := Iff.rfl

lemma IsInvertedBy.iff_map_le_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W.map F ≤ isomorphisms D := by
  rw [iff_le_inverseImage_isomorphisms, map_le_iff (RespectsIso.isomorphisms D)]

lemma IsInvertedBy.map_iff {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
    (W.map F).IsInvertedBy G ↔ W.IsInvertedBy (F ⋙ G) := by
  simp only [IsInvertedBy.iff_map_le_isomorphisms, map_map]

end MorphismProperty

end CategoryTheory
