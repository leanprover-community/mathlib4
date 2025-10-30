/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# The model category structure on Over categories

-/

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

-- to be moved
variable {S} in
lemma CategoryTheory.CommSq.HasLift.over {X₁ X₂ X₃ X₄ : Over S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} {sq : CommSq t l r b}
    [CommSq.HasLift (f := t.left) (i := l.left) (p := r.left) (g := b.left)
      (sq.map (Over.forget _))] :
    sq.HasLift := by
  let sq' := sq.map (Over.forget _)
  dsimp at sq'
  exact ⟨⟨{
    l := Over.homMk sq'.lift
      (by rw [← Over.w b, ← sq'.fac_right_assoc, Over.w r])
  }⟩⟩

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

instance : CategoryWithCofibrations (Over S) where
  cofibrations := (cofibrations C).over

lemma cofibrations_over_def :
    cofibrations (Over S) = (cofibrations C).over := rfl

lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff]
  rfl

instance {X Y : Over S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.left := by
  rwa [← cofibrations_over_iff]

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Over S)).IsStableUnderRetracts := by
  rw [cofibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

instance : CategoryWithFibrations (Over S) where
  fibrations := (fibrations C).over

lemma fibrations_over_def :
    fibrations (Over S) = (fibrations C).over := rfl

lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff]
  rfl

instance {X Y : Over S} (f : X ⟶ Y) [Fibration f] : Fibration f.left := by
  rwa [← fibrations_over_iff]

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Over S)).IsStableUnderRetracts := by
  rw [fibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

instance : CategoryWithWeakEquivalences (Over S) where
  weakEquivalences := (weakEquivalences C).over

lemma weakEquivalences_over_def :
    weakEquivalences (Over S) = (weakEquivalences C).over := rfl

lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff]
  rfl

instance {X Y : Over S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.left := by
  rwa [← weakEquivalences_over_iff]

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Over S)).IsStableUnderRetracts := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

lemma trivialCofibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Over S) = (trivialCofibrations C).over := rfl

lemma trivialFibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Over S) = (trivialFibrations C).over := rfl

-- to be moved
variable {S} in
lemma _root_.CategoryTheory.HasLiftingProperty.over {A B X Y : Over S}
    (i : A ⟶ B) (p : X ⟶ Y) [HasLiftingProperty i.left p.left] :
    HasLiftingProperty i p := ⟨fun _ ↦ .over⟩

-- to be moved
instance _root_.CategoryTheory.MorphismProperty.HasFactorization.over
    (W₁ W₂ : MorphismProperty C) [W₁.HasFactorization W₂] (S : C) :
    (W₁.over (X := S)).HasFactorization W₂.over where
  nonempty_mapFactorizationData {X Y} f := by
    let hf := W₁.factorizationData W₂ f.left
    exact ⟨{
      Z := Over.mk (hf.p ≫ Y.hom)
      i := Over.homMk hf.i
      p := Over.homMk hf.p
      hi := hf.hi
      hp := hf.hp
    }⟩

instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Over S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Over S)).HasFactorization (fibrations (Over S)) := by
  rw [fibrations_over_def, trivialCofibrations_over_eq]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Over S)).HasFactorization (trivialFibrations (Over S)) := by
  rw [cofibrations_over_def, trivialFibrations_over_eq]
  infer_instance

end

instance ModelCategory.over [ModelCategory C] : ModelCategory (Over S) where
  cm4a _ _ _ _ _ := CategoryTheory.HasLiftingProperty.over _ _
  cm4b _ _ _ _ _ := CategoryTheory.HasLiftingProperty.over _ _

end HomotopicalAlgebra
