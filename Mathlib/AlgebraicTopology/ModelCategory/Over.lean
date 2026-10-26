/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# The model category structure on Over and Under categories

Let `C` be a model category. For any `S : C`, we define
a model category structure on the category `Over S`:
a morphism `X ⟶ Y` in `Over S` is a cofibration
(resp. a fibration, a weak equivalence) if the
underlying morphism `f.left : X.left ⟶ Y.left` is.
(Apart from the existence of (finite) limits
from `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic`, the verification
of the axioms is straightforward.)

We also proceed to the dual construction for `Under` categories.

-/

public section

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

instance : CategoryWithCofibrations (Over S) where
  cofibrations := (cofibrations C).over

instance : CategoryWithCofibrations (Under S) where
  cofibrations := (cofibrations C).under

lemma cofibrations_over_def :
    cofibrations (Over S) = (cofibrations C).over := rfl

lemma cofibrations_under_def :
    cofibrations (Under S) = (cofibrations C).under := rfl

lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]

lemma cofibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := by
  simp only [cofibration_iff, cofibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Over S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.left := by
  rwa [← cofibrations_over_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.right := by
  rwa [← cofibrations_under_iff]

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Over S)).IsStableUnderRetracts := by
  rw [cofibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Under S)).IsStableUnderRetracts := by
  rw [cofibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

instance : CategoryWithFibrations (Over S) where
  fibrations := (fibrations C).over

instance : CategoryWithFibrations (Under S) where
  fibrations := (fibrations C).under

lemma fibrations_over_def :
    fibrations (Over S) = (fibrations C).over := rfl

lemma fibrations_under_def :
    fibrations (Under S) = (fibrations C).under := rfl

lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]

lemma fibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := by
  simp only [fibration_iff, fibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Over S} (f : X ⟶ Y) [Fibration f] : Fibration f.left := by
  rwa [← fibrations_over_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Fibration f] : Fibration f.right := by
  rwa [← fibrations_under_iff]

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Over S)).IsStableUnderRetracts := by
  rw [fibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Under S)).IsStableUnderRetracts := by
  rw [fibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

instance : CategoryWithWeakEquivalences (Over S) where
  weakEquivalences := (weakEquivalences C).over

instance : CategoryWithWeakEquivalences (Under S) where
  weakEquivalences := (weakEquivalences C).under

lemma weakEquivalences_over_def :
    weakEquivalences (Over S) = (weakEquivalences C).over := rfl

lemma weakEquivalences_under_def :
    weakEquivalences (Under S) = (weakEquivalences C).under := rfl

lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]

lemma weakEquivalences_under_iff {X Y : Under S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := by
  simp only [weakEquivalence_iff, weakEquivalences_under_def, MorphismProperty.under_iff]

instance {X Y : Over S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.left := by
  rwa [← weakEquivalences_over_iff]

instance {X Y : Under S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.right := by
  rwa [← weakEquivalences_under_iff]

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Over S)).IsStableUnderRetracts := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Under S)).IsStableUnderRetracts := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

lemma trivialCofibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Over S) = (trivialCofibrations C).over := rfl

lemma trivialCofibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Under S) = (trivialCofibrations C).under := rfl

lemma trivialFibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Over S) = (trivialFibrations C).over := rfl

lemma trivialFibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Under S) = (trivialFibrations C).under := rfl

instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Over S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Under S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Over S)).HasFactorization (fibrations (Over S)) := by
  rw [fibrations_over_def, trivialCofibrations_over_eq]
  infer_instance

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Under S)).HasFactorization (fibrations (Under S)) := by
  rw [fibrations_under_def, trivialCofibrations_under_eq]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Over S)).HasFactorization (trivialFibrations (Over S)) := by
  rw [cofibrations_over_def, trivialFibrations_over_eq]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Under S)).HasFactorization (trivialFibrations (Under S)) := by
  rw [cofibrations_under_def, trivialFibrations_under_eq]
  infer_instance

end

instance ModelCategory.over [ModelCategory C] : ModelCategory (Over S) where
  cm4a _ _ _ _ _ := .over _ _
  cm4b _ _ _ _ _ := .over _ _

instance ModelCategory.under [ModelCategory C] : ModelCategory (Under S) where
  cm4a _ _ _ _ _ := .under _ _
  cm4b _ _ _ _ _ := .under _ _

end HomotopicalAlgebra
