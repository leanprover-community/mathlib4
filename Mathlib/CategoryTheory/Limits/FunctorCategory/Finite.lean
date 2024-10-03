/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Functor categories have finite limits when the target category does

These declarations cannot be in the file `Mathlib.CategoryTheory.Limits.FunctorCategory` because
that file shouldn't import `Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts`.
-/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {K : Type*} [Category K]

instance [HasFiniteLimits C] : HasFiniteLimits (K ⥤ C) := ⟨fun _ ↦ inferInstance⟩

instance [HasFiniteProducts C] : HasFiniteProducts (K ⥤ C) := ⟨inferInstance⟩

instance [HasFiniteColimits C] : HasFiniteColimits (K ⥤ C) := ⟨fun _ ↦ inferInstance⟩

instance [HasFiniteCoproducts C] : HasFiniteCoproducts (K ⥤ C) := ⟨inferInstance⟩

/-- `F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`. -/
def preservesFiniteLimitsOfEvaluation {D : Type*} [Category D] {E : Type*} [Category E]
    (F : C ⥤ D ⥤ E) (h : ∀ d : D, PreservesFiniteLimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteLimits F :=
  ⟨fun J _ _ => preservesLimitsOfShapeOfEvaluation F J fun k => (h k).preservesFiniteLimits _⟩

/-- `F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`. -/
def preservesFiniteColimitsOfEvaluation {D : Type*} [Category D] {E : Type*} [Category E]
    (F : C ⥤ D ⥤ E) (h : ∀ d : D, PreservesFiniteColimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteColimits F :=
  ⟨fun J _ _ => preservesColimitsOfShapeOfEvaluation F J fun k => (h k).preservesFiniteColimits _⟩

end CategoryTheory.Limits
