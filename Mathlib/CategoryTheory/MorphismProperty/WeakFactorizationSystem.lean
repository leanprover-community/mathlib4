/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Weak factorization systems

In this file, we introduce the notion of weak factorization system,
which is a property of two classes of morphisms `W₁` and `W₂` in
a category `C`. The type class `IsWeakFactorizationSystem W₁ W₂` asserts
that `W₁` is exactly `W₂.llp`, `W₂` is exactly `W₁.rlp`,
and any morphism in `C` can be factored a `i ≫ p` with `W₁ i` and `W₂ p`.

## References
* https://ncatlab.org/nlab/show/weak+factorization+system

-/

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W₁ W₂ : MorphismProperty C)

/-- Two classes of morphisms `W₁` and `W₂` in a category `C` form a weak
factorization system if `W₁` is exactly `W₂.llp`, `W₂` is exactly `W₁.rlp`,
and any morphism can be factored a `i ≫ p` with `W₁ i` and `W₂ p`. -/
class IsWeakFactorizationSystem : Prop where
  rlp : W₁.rlp = W₂
  llp : W₂.llp = W₁
  hasFactorization : HasFactorization W₁ W₂ := by infer_instance

namespace IsWeakFactorizationSystem

attribute [instance] hasFactorization

lemma mk' [HasFactorization W₁ W₂]
    [W₁.IsStableUnderRetracts] [W₂.IsStableUnderRetracts]
    (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
      W₁ i → W₂ p → HasLiftingProperty i p) :
    IsWeakFactorizationSystem W₁ W₂ where
  rlp := rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hp _ _ _ hi ↦ h _ _ hi hp)
  llp := llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hi _ _ _ hp ↦ h _ _ hi hp)

end IsWeakFactorizationSystem

section

variable [IsWeakFactorizationSystem W₁ W₂]

lemma rlp_eq_of_wfs : W₁.rlp = W₂ := IsWeakFactorizationSystem.rlp

lemma llp_eq_of_wfs : W₂.llp = W₁ := IsWeakFactorizationSystem.llp

variable {W₁ W₂} in
lemma hasLiftingProperty_of_wfs {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : W₁ i) (hp : W₂ p) : HasLiftingProperty i p :=
  (llp_eq_of_wfs W₁ W₂ ▸ hi) p hp

end

end CategoryTheory.MorphismProperty
