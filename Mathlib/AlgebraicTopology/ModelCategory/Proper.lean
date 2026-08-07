/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Proper model categories

In this file, we define typeclasses `IsLeftProper` and `IsRightProper` for
model categories. A model category is right proper when equivalences
are stable under pullbacks by fibrations (resp. left proper when equivalences
are stable under pushouts by cofibrations).


## References
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]
* https://ncatlab.org/nlab/show/proper+model+category

-/

public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type*} [Category* C]

variable (C) in
/-- A model category is right proper when the pullback of a weak equivalence
by a fibration is a weak equivalence. -/
class IsRightProper [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] : Prop where
  isStableUnderBaseChangeAlong {E B : C} (p : E ⟶ B) [Fibration p] :
    (weakEquivalences C).IsStableUnderBaseChangeAlong p

variable (C) in
/-- A model category is left proper when the pushout of a weak equivalence
by a cofibration is a weak equivalence. -/
class IsLeftProper [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] : Prop where
  isStableUnderCobaseChangeAlong {X Y : C} (i : X ⟶ Y) [Cofibration i] :
    (weakEquivalences C).IsStableUnderCobaseChangeAlong i

namespace IsRightProper

attribute [instance] isStableUnderBaseChangeAlong

variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] [IsRightProper C]

variable {E' B' E B : C}

lemma weakEquivalence {t : E' ⟶ B'} {l : E' ⟶ E} {r : B' ⟶ B} {b : E ⟶ B}
    [WeakEquivalence r] [Fibration b] (sq : IsPullback t l r b) :
    WeakEquivalence l :=
  (weakEquivalence_iff ..).mpr
    (MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
      sq (mem_weakEquivalences r))

lemma weakEquivalence' {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
    [WeakEquivalence b] [Fibration r] (sq : IsPullback t l r b) :
    WeakEquivalence t :=
  weakEquivalence sq.flip

instance (p : E ⟶ B) (w : B' ⟶ B) [Fibration p] [WeakEquivalence w]
    [HasPullback w p] :
    WeakEquivalence (pullback.snd w p) :=
  weakEquivalence (IsPullback.of_hasPullback w p)

instance (p : E ⟶ B) (w : B' ⟶ B) [Fibration p] [WeakEquivalence w]
    [HasPullback p w] :
    WeakEquivalence (pullback.fst p w) :=
  weakEquivalence' (IsPullback.of_hasPullback p w)

instance [(fibrations C).IsStableUnderBaseChange]
    (p : E ⟶ B) {X Y : C} (w : X ⟶ Y) (a : Y ⟶ B) [HasPullback p a] [HasPullback p (w ≫ a)]
    [WeakEquivalence w] [Fibration p] :
    WeakEquivalence (pullback.map p (w ≫ a) p a (𝟙 _) w (𝟙 _) (by simp) (by simp)) :=
  have :
      IsPullback (pullback.map p (w ≫ a) p a (𝟙 _) w (𝟙 _) (by simp) (by simp))
        (pullback.snd _ _) (pullback.snd _ _) w :=
    .of_right (by simpa using IsPullback.of_hasPullback p (w ≫ a)) (by cat_disch)
      (.of_hasPullback p a)
  weakEquivalence' this

instance [(fibrations C).IsStableUnderBaseChange]
    (p : E ⟶ B) {X Y : C} (w : X ⟶ Y) (a : Y ⟶ B) [HasPullback a p] [HasPullback (w ≫ a) p]
    [WeakEquivalence w] [Fibration p] :
    WeakEquivalence (pullback.map (w ≫ a) p a p w (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
  have :
      IsPullback (pullback.fst _ _)
        (pullback.map (w ≫ a) p a p w (𝟙 _) (𝟙 _) (by simp) (by simp)) w (pullback.fst _ _) :=
    .of_bot (by simpa using IsPullback.of_hasPullback (w ≫ a) p) (by cat_disch)
      (.of_hasPullback a p)
  weakEquivalence this

end IsRightProper

namespace IsLeftProper

attribute [instance] isStableUnderCobaseChangeAlong

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] [IsLeftProper C]

variable {X Y X' Y' : C}

lemma weakEquivalence {t : X ⟶ Y} {l : X ⟶ X'} {r : Y ⟶ Y'} {b : X' ⟶ Y'}
    [WeakEquivalence l] [Cofibration t] (sq : IsPushout t l r b) :
    WeakEquivalence r :=
  (weakEquivalence_iff ..).mpr
    (MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPushout
        sq (mem_weakEquivalences l))

lemma weakEquivalence' {t : X ⟶ X'} {l : X ⟶ Y} {r : X' ⟶ Y'} {b : Y ⟶ Y'}
    [WeakEquivalence t] [Cofibration l] (sq : IsPushout t l r b) :
    WeakEquivalence b :=
  weakEquivalence sq.flip

instance (i : X ⟶ Y) (w : X ⟶ X') [Cofibration i] [WeakEquivalence w] [HasPushout i w] :
    WeakEquivalence (pushout.inl i w) :=
  weakEquivalence (IsPushout.of_hasPushout i w)

instance (i : X ⟶ Y) (w : X ⟶ X') [Cofibration i] [WeakEquivalence w] [HasPushout w i] :
    WeakEquivalence (pushout.inr w i) :=
  weakEquivalence' (IsPushout.of_hasPushout w i)

instance [(cofibrations C).IsStableUnderCobaseChange]
    (i : X ⟶ Y) {W Z : C} (w : W ⟶ Z) (a : X ⟶ W) [HasPushout i a] [HasPushout i (a ≫ w)]
    [WeakEquivalence w] [Cofibration i] :
    WeakEquivalence (pushout.map i a i (a ≫ w) (𝟙 _) w (𝟙 _) (by simp) (by simp)) :=
  have :
      IsPushout (pushout.inr _ _) w
        (pushout.map i a i (a ≫ w) (𝟙 _) w (𝟙 _) (by simp) (by simp)) (pushout.inr _ _) :=
    IsPushout.of_top (by simpa using IsPushout.of_hasPushout i (a ≫ w)) (by cat_disch)
      (IsPushout.of_hasPushout i a)
  weakEquivalence this

instance [(cofibrations C).IsStableUnderCobaseChange]
    (i : X ⟶ Y) {W Z : C} (w : W ⟶ Z) (a : X ⟶ W) [HasPushout a i] [HasPushout (a ≫ w) i]
    [WeakEquivalence w] [Cofibration i] :
    WeakEquivalence (pushout.map a i (a ≫ w) i w (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
  have :
      IsPushout w (pushout.inl _ _) (pushout.inl _ _)
        (pushout.map a i (a ≫ w) i w (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    IsPushout.of_left (by simpa using (IsPushout.of_hasPushout (a ≫ w) i)) (by cat_disch)
      (IsPushout.of_hasPushout a i)
  weakEquivalence' this

end IsLeftProper

lemma isRightProper_op_iff [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] :
    IsRightProper Cᵒᵖ ↔ IsLeftProper C := by
  refine ⟨fun _ ↦ ⟨fun {X₁ X₂} t _ ↦ ⟨fun {X₃ X₄ b r l} sq hl ↦ ?_⟩⟩,
    fun _ ↦ ⟨fun {X₁ X₂} b _ ↦ ⟨fun {X₃ X₄ t l r} sq hr ↦ ?_⟩⟩⟩
  · rw [← weakEquivalence_iff] at hl ⊢
    rw [← weakEquivalences_op_iff]
    exact IsRightProper.weakEquivalence sq.op
  · rw [← weakEquivalence_iff] at hr ⊢
    rw [← weakEquivalences_unop_iff]
    exact IsLeftProper.weakEquivalence sq.unop

lemma isLeftProper_op_iff [CategoryWithFibrations C] [CategoryWithWeakEquivalences C] :
    IsLeftProper Cᵒᵖ ↔ IsRightProper C := by
  refine ⟨fun _ ↦ ⟨fun {X₁ X₂} t _ ↦ ⟨fun {X₃ X₄ b r l} sq hl ↦ ?_⟩⟩,
    fun _ ↦ ⟨fun {X₁ X₂} b _ ↦ ⟨fun {X₃ X₄ t l r} sq hr ↦ ?_⟩⟩⟩
  · rw [← weakEquivalence_iff] at hl ⊢
    rw [← weakEquivalences_op_iff]
    exact IsLeftProper.weakEquivalence sq.op
  · rw [← weakEquivalence_iff] at hr ⊢
    rw [← weakEquivalences_unop_iff]
    exact IsRightProper.weakEquivalence sq.unop

instance [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsLeftProper C] :
    IsRightProper Cᵒᵖ := by
  rwa [isRightProper_op_iff]

instance [CategoryWithFibrations C] [CategoryWithWeakEquivalences C] [IsRightProper C] :
    IsLeftProper Cᵒᵖ := by
  rwa [isLeftProper_op_iff]

end HomotopicalAlgebra
