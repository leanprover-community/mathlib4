/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# The retract argument

Let `W₁` and `W₂` be classes of morphisms in a category `C` such that
any morphism can be factored as a morphism in `W₁` followed by
a morphism in `W₂` (this is `HasFactorization W₁ W₂`).
If `W₁` has the left lifting property with respect to `W₂`
(i.e. `W₁ ≤ W₂.llp`, or equivalently `W₂ ≤ W₁.rlp`),
then `W₂.llp = W₁` if `W₁` is stable under retracts,
and `W₁.rlp = W₂` if `W₂` is.

## Reference
- https://ncatlab.org/nlab/show/weak+factorization+system#retract_argument

-/

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- If `i : X ⟶ Y` and `p : Y ⟶ Z` are composable morphisms,
and `i ≫ p` has the left lifting property with respect to `p`,
then `i ≫ p` is a retract of `i`. -/
noncomputable def RetractArrow.ofLeftLiftingProperty
    {X Y Z : C} (i : X ⟶ Y) (p : Y ⟶ Z)
    [HasLiftingProperty (i ≫ p) p] : RetractArrow (i ≫ p) i :=
  have sq : CommSq i (i ≫ p) p (𝟙 _) := ⟨by simp⟩
  { i := Arrow.homMk (u := 𝟙 X) (v := sq.lift) (by simp)
    r := Arrow.homMk (u := 𝟙 X) (v := p) (by simp) }

/-- If `i : X ⟶ Y` and `p : Y ⟶ Z` are composable morphisms,
and `i ≫ p` has the right lifting property with respect to `i`,
then `i ≫ p` is a retract of `p`. -/
noncomputable def RetractArrow.ofRightLiftingProperty
    {X Y Z : C} (i : X ⟶ Y) (p : Y ⟶ Z)
    [HasLiftingProperty i (i ≫ p)] : RetractArrow (i ≫ p) p :=
  have sq : CommSq (𝟙 _) i (i ≫ p) p := ⟨by simp⟩
  { i := Arrow.homMk (u := i) (v := 𝟙 _) (by simp)
    r := Arrow.homMk (u := sq.lift) (v := 𝟙 _) (by simp) }

namespace MorphismProperty

variable {W₁ W₂ : MorphismProperty C}

lemma llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    [HasFactorization W₁ W₂] [W₁.IsStableUnderRetracts] (h₁ : W₁ ≤ W₂.llp) :
    W₂.llp = W₁ :=
  le_antisymm (by
    intro A B i hi
    have h := factorizationData W₁ W₂ i
    have : HasLiftingProperty (h.i ≫ h.p) h.p := by simpa using hi _ h.hp
    simpa using of_retract (RetractArrow.ofLeftLiftingProperty h.i h.p) h.hi) h₁

lemma rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    [HasFactorization W₁ W₂] [W₂.IsStableUnderRetracts] (h₂ : W₂ ≤ W₁.rlp) :
    W₁.rlp = W₂ :=
  le_antisymm (by
    intro X Y p hp
    have h := factorizationData W₁ W₂ p
    have : HasLiftingProperty h.i (h.i ≫ h.p) := by simpa using hp _ h.hi
    simpa using of_retract (RetractArrow.ofRightLiftingProperty h.i h.p) h.hp) h₂

end MorphismProperty

end CategoryTheory
