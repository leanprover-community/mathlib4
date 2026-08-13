/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Pushout-products in adhesive categories

This file proves that the pushout-product of monomorphisms in an adhesive cartesian monoidal
category is a monomorphism.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits MonoidalCategory Functor.PushoutObjObj

namespace Functor.PushoutObjObj

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {X₁ Y₁ : C₁} {X₂ Y₂ : C₂}
  {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}

/-- The induced pushout map (Leibniz pushout) of an `F.PushoutObjObj` is a monomorphism if its
naturality square is a pullback and the morphisms being pulled back are monomorphisms. -/
theorem mono_ι_of_isPullback [Adhesive C₃] (sq : F.PushoutObjObj f₁ f₂)
    (h : IsPullback ((F.map f₁).app X₂) ((F.obj X₁).map f₂) ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂))
    [Mono ((F.obj Y₁).map f₂)] [Mono ((F.map f₁).app Y₂)] : Mono sq.ι := by
  rw [show sq.ι = sq.isPushout.desc _ _ h.w by ext <;> simp]
  exact sq.isPushout.desc_mono_of_isPullback h

end Functor.PushoutObjObj

namespace MonoidalCategory.Arrow.PushoutProduct

universe v u

variable {C : Type u} [Category.{v} C] [HasPushouts C]

open CartesianMonoidalCategory in
/-- The pushout-product of two monomorphisms in an adhesive cartesian monoidal category is a
monomorphism. -/
instance [CartesianMonoidalCategory C] [Adhesive C] {X Y : Arrow C} [Mono X.hom] [Mono Y.hom] :
    Mono (X □ Y).hom := by
  have : Mono (((curriedTensor C).obj X.right).map Y.hom) := (tensorLeft X.right).map_mono Y.hom
  have : Mono (((curriedTensor C).map X.hom).app Y.right) := (tensorRight Y.right).map_mono X.hom
  refine mono_ι_of_isPullback (ofHasPushout (curriedTensor C) X.hom Y.hom)
    (IsPullback.mk' (whisker_exchange _ _).symm ?_ ?_)
  · intro _ _ _ h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂ =≫ fst _ _
    · simpa using h₁ =≫ snd _ _
  · intro _ a b h
    refine ⟨lift (b ≫ fst _ _) (a ≫ snd _ _), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simpa using (h =≫ fst _ _).symm
      · simp
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using h =≫ snd _ _

end MonoidalCategory.Arrow.PushoutProduct

end CategoryTheory
