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

/-- If `i ≫ p = f`, and `f` has the left lifting property with respect to `p`,
then `f` is a retract of `i`. -/
noncomputable def RetractArrow.ofLeftLiftingProperty
    {X Y Z : C} {f : X ⟶ Z} {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = f)
    [HasLiftingProperty f p] : RetractArrow f i :=
  have sq : CommSq i f p (𝟙 _) := ⟨by simp [h]⟩
  { i := Arrow.homMk (𝟙 X) sq.lift
    r := Arrow.homMk (𝟙 X) p }

/-- If `i ≫ p = f`, and `f` has the right lifting property with respect to `i`,
then `f` is a retract of `p`. -/
noncomputable def RetractArrow.ofRightLiftingProperty
    {X Y Z : C} {f : X ⟶ Z} {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = f)
    [HasLiftingProperty i f] : RetractArrow f p :=
  have sq : CommSq (𝟙 _) i f p := ⟨by simp [h]⟩
  { i := Arrow.homMk i (𝟙 _)
    r := Arrow.homMk sq.lift (𝟙 _) }

namespace MorphismProperty

variable {W₁ W₂ : MorphismProperty C}

lemma llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    [HasFactorization W₁ W₂] [W₁.IsStableUnderRetracts] (h₁ : W₁ ≤ W₂.llp) :
    W₂.llp = W₁ :=
  le_antisymm (fun A B i hi ↦ by
    have h := factorizationData W₁ W₂ i
    have := hi _ h.hp
    simpa using of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi) h₁

lemma rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    [HasFactorization W₁ W₂] [W₂.IsStableUnderRetracts] (h₂ : W₂ ≤ W₁.rlp) :
    W₁.rlp = W₂ :=
  le_antisymm (fun X Y p hp ↦ by
    have h := factorizationData W₁ W₂ p
    have := hp _ h.hi
    simpa using of_retract (RetractArrow.ofRightLiftingProperty h.fac) h.hp) h₂

end MorphismProperty

end CategoryTheory
