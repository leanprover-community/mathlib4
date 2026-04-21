/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# A trick by Joyal

In order to construct a model category, we may sometimes have basically
proven all the axioms with the exception of the left lifting property
of cofibrations with respect to trivial fibrations. A trick by Joyal
allows to obtain this lifting property under suitable assumptions,
namely that cofibrations are stable under composition and cobase change.
(The dual result is also formalized.)

## References
* [John F. Jardine, Simplicial presheaves][jardine-1987]

-/
set_option backward.defeqAttrib.useBackward true

public section

open CategoryTheory Category Limits MorphismProperty

namespace HomotopicalAlgebra

namespace ModelCategory

variable {C : Type*} [Category* C]
  [CategoryWithCofibrations C] [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]
  [(weakEquivalences C).HasTwoOutOfThreeProperty]

set_option backward.isDefEq.respectTransparency false in
/-- Joyal's trick: that cofibrations have the left lifting property
with respect to trivial fibrations follows from the left lifting property
of trivial cofibrations with respect to fibrations and a few other
consequences of the model categories axioms. -/
lemma hasLiftingProperty_of_joyalTrick
    [HasFactorization (cofibrations C) (trivialFibrations C)] [HasPushouts C]
    [(cofibrations C).IsStableUnderComposition] [(cofibrations C).IsStableUnderCobaseChange]
    (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
      [Cofibration i] [WeakEquivalence i] [Fibration p], HasLiftingProperty i p)
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    let h := factorizationData (cofibrations C) (trivialFibrations C)
      (pushout.desc p g sq.w)
    have sq' : CommSq (𝟙 X) (pushout.inl _ _ ≫ h.i) p h.p := .mk
    have h₁ : WeakEquivalence ((pushout.inl f i ≫ h.i) ≫ h.p) := by simpa
    have h₂ := comp_mem _ _ _ ((cofibrations C).of_isPushout
      (IsPushout.of_hasPushout f i) (mem_cofibrations i)) h.hi
    rw [← cofibration_iff] at h₂
    have : WeakEquivalence (pushout.inl f i ≫ h.i) := by
      rw [weakEquivalence_iff] at h₁ ⊢
      exact of_postcomp _ _ _ h.hp.2 h₁
    exact ⟨⟨{ l := pushout.inr f i ≫ h.i ≫ sq'.lift
              fac_left := by
                simpa only [assoc, comp_id, pushout.condition_assoc] using
                  f ≫= sq'.fac_left }⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Joyal's trick (dual): that trivial cofibrations have the left lifting
property with respect to fibrations follows from the left lifting property
of cofibrations with respect to trivial fibrations and a few other
consequences of the model categories axioms. -/
lemma hasLiftingProperty_of_joyalTrickDual
    [HasFactorization (trivialCofibrations C) (fibrations C)] [HasPullbacks C]
    [(fibrations C).IsStableUnderComposition] [(fibrations C).IsStableUnderBaseChange]
    (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
      [Cofibration i] [WeakEquivalence p] [Fibration p], HasLiftingProperty i p)
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence i] :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    let h := factorizationData (trivialCofibrations C) (fibrations C)
      (pullback.lift f i sq.w)
    have sq' : CommSq h.i i (h.p ≫ pullback.snd _ _) (𝟙 B) := .mk
    have h₁ : WeakEquivalence (h.i ≫ h.p ≫ pullback.snd p g) := by simpa
    have h₂ := comp_mem _ _ _ h.hp ((fibrations C).of_isPullback
      (IsPullback.of_hasPullback p g) (mem_fibrations p))
    rw [← fibration_iff] at h₂
    have : WeakEquivalence (h.p ≫ pullback.snd p g) := by
      rw [weakEquivalence_iff] at h₁ ⊢
      exact of_precomp _ _ _ h.hi.2 h₁
    exact ⟨⟨{ l := sq'.lift ≫ h.p ≫ pullback.fst p g
              fac_right := by
                rw [assoc, assoc, pullback.condition, reassoc_of% sq'.fac_right] }⟩⟩

end ModelCategory

end HomotopicalAlgebra
