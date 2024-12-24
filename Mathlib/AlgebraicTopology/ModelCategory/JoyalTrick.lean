/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# A trick by Joyal

In order to construct a model category, we may sometimes have basically
proven all the axioms with the exception of the left lifting property
of cofibrations with respect to trivial fibrations. A trick by Joyal
allows to obtain this lifting property under suitable assumptions,
namely that cofibrations are stable under composition and cobase change.

## References
* [John F. Jardine, Simplicial presheaves][jardine-1987]

-/

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

namespace ModelCategory

variable {C : Type*} [Category C]
  [CategoryWithCofibrations C] [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]
  [MorphismProperty.HasFactorization (cofibrations C) (trivialFibrations C)]
  [(weakEquivalences C).HasTwoOutOfThreeProperty] [HasPushouts C]
  [(cofibrations C).IsStableUnderComposition] [(cofibrations C).IsStableUnderCobaseChange]
  [∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p],
      HasLiftingProperty i p]

lemma joyal_trick {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
      (pushout.desc p g sq.w)
    have sq' : CommSq (𝟙 X) (pushout.inl _ _ ≫ h.i) p h.p := ⟨by simp⟩
    have h₁ : WeakEquivalence ((pushout.inl f i ≫ h.i) ≫ h.p) := by simpa
    have h₂ := MorphismProperty.comp_mem _ _ _
      ((cofibrations C).of_isPushout (IsPushout.of_hasPushout f i) (mem_cofibrations i)) h.hi
    rw [← cofibration_iff] at h₂
    have : WeakEquivalence (pushout.inl f i ≫ h.i) := by
      rw [weakEquivalence_iff] at h₁ ⊢
      exact MorphismProperty.of_postcomp _ _ _ h.hp.2 h₁
    exact
      ⟨⟨{ l := pushout.inr f i ≫ h.i ≫ sq'.lift
          fac_left := by
            have := sq'.fac_left
            simp only [assoc] at this
            rw [← pushout.condition_assoc, this, comp_id] }⟩⟩

end ModelCategory

end HomotopicalAlgebra
