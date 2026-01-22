/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick
public import Mathlib.AlgebraicTopology.ModelCategory.Smith.Lemma19
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteCompositionCoproducts
public import Mathlib.CategoryTheory.Presentable.SmallObject

/-!
# Smith's theorem

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty SmallObject

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

def CategoryWithSmithStructure
    [IsLocallyPresentable.{w} C]
    {W : MorphismProperty C} {I : MorphismProperty C}
    [MorphismProperty.IsSmall.{w} I]
    [W.HasTwoOutOfThreeProperty] [W.IsStableUnderRetracts]
    [IsStableUnderTransfiniteComposition.{w} (I.rlp.llp ⊓ W)]
    [IsStableUnderCobaseChange (I.rlp.llp ⊓ W)]
    (_ : I.rlp ≤ W) (_ : I ≤ solutionSetCondition.{w} W) := C

variable [IsLocallyPresentable.{w} C]
  {W : MorphismProperty C} {I : MorphismProperty C}
  [MorphismProperty.IsSmall.{w} I]
  [W.HasTwoOutOfThreeProperty] [W.IsStableUnderRetracts]
  [IsStableUnderTransfiniteComposition.{w} (I.rlp.llp ⊓ W)]
  [IsStableUnderCobaseChange (I.rlp.llp ⊓ W)]
  (hIW₁ : I.rlp ≤ W) (hIW₃ : I ≤ solutionSetCondition.{w} W)

namespace CategoryWithSmithStructure

instance : Category (CategoryWithSmithStructure hIW₁ hIW₃) :=
  inferInstanceAs (Category C)

instance : IsLocallyPresentable.{w} (CategoryWithSmithStructure hIW₁ hIW₃) :=
  inferInstanceAs (IsLocallyPresentable.{w} C)

instance : CategoryWithCofibrations (CategoryWithSmithStructure hIW₁ hIW₃) where
  cofibrations := I.rlp.llp

instance : CategoryWithWeakEquivalences (CategoryWithSmithStructure hIW₁ hIW₃) where
  weakEquivalences := W

instance : CategoryWithFibrations (CategoryWithSmithStructure hIW₁ hIW₃) where
  fibrations := (I.rlp.llp ⊓ W).rlp

@[simp]
lemma cofibrations_eq :
    cofibrations (CategoryWithSmithStructure hIW₁ hIW₃) = I.rlp.llp := rfl

@[simp]
lemma weakEquivalences_eq :
    weakEquivalences (CategoryWithSmithStructure hIW₁ hIW₃) = W := rfl

@[simp]
lemma fibrations_eq :
    fibrations (CategoryWithSmithStructure hIW₁ hIW₃) = (I.rlp.llp ⊓ W).rlp := rfl

instance : HasFiniteColimits (CategoryWithSmithStructure hIW₁ hIW₃) := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal C
  have := hasColimitsOfSizeShrink.{0, 0, w, w} C
  change HasFiniteColimits C
  infer_instance

instance :
    (weakEquivalences (CategoryWithSmithStructure hIW₁ hIW₃)).HasTwoOutOfThreeProperty := by
  simpa

instance :
    (weakEquivalences (CategoryWithSmithStructure hIW₁ hIW₃)).IsStableUnderRetracts := by
  simpa

instance :
    (cofibrations (CategoryWithSmithStructure hIW₁ hIW₃)).IsStableUnderRetracts := by
  simp only [cofibrations_eq]
  infer_instance

instance :
    (cofibrations (CategoryWithSmithStructure hIW₁ hIW₃)).IsStableUnderCobaseChange := by
  simp only [cofibrations_eq]
  infer_instance

instance :
    (cofibrations (CategoryWithSmithStructure hIW₁ hIW₃)).IsMultiplicative := by
  simp only [cofibrations_eq]
  infer_instance

instance :
    (fibrations (CategoryWithSmithStructure hIW₁ hIW₃)).IsStableUnderRetracts := by
  simp only [fibrations_eq]
  infer_instance

instance {A B X Y : CategoryWithSmithStructure hIW₁ hIW₃}
    (i : A ⟶ B) (p : X ⟶ Y) [hi₁ : Cofibration i] [hi₂ : WeakEquivalence i]
    [hp : Fibration p] :
    HasLiftingProperty i p := by
  rw [cofibration_iff, cofibrations_eq] at hi₁
  rw [weakEquivalence_iff, weakEquivalences_eq] at hi₂
  rw [fibration_iff, fibrations_eq] at hp
  exact hp _ ⟨hi₁, hi₂⟩

instance : (cofibrations (CategoryWithSmithStructure hIW₁ hIW₃)).HasFunctorialFactorization
    (trivialFibrations (CategoryWithSmithStructure hIW₁ hIW₃)) := by
  have le : I.rlp ≤ (I.rlp.llp ⊓ W).rlp ⊓ W := by
    simp only [le_inf_iff]
    exact ⟨by simp [← le_llp_iff_le_rlp], hIW₁⟩
  simpa [trivialFibrations] using HasFunctorialFactorization.of_le le_rfl le

open lemma_1_9 in
instance : (trivialCofibrations (CategoryWithSmithStructure hIW₁ hIW₃)).HasFactorization
    (fibrations (CategoryWithSmithStructure hIW₁ hIW₃)) := by
  obtain ⟨κ, _, hκ⟩ : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∀ {A B : C} (i : A ⟶ B) (hi : I i), IsCardinalPresentable A κ := by
    choose κ' _ hκ' using fun (x : I.toSet) ↦ IsPresentable.exists_cardinal.{w} x.1.left
    obtain ⟨κ, _, hκ⟩ :=
      HasCardinalLT.exists_regular_cardinal_forall (fun x ↦ (κ' x).ord.ToType)
    have : Fact κ.IsRegular := ⟨by assumption⟩
    refine ⟨κ, inferInstance, fun {A _} i hi ↦ ?_⟩
    have : IsCardinalPresentable A (κ' ⟨Arrow.mk i, hi⟩) := hκ' ⟨i, hi⟩
    exact isCardinalPresentable_of_le _ (by simpa using (hκ ⟨i, hi⟩).le)
  have : OrderBot κ.ord.ToType := Cardinal.toTypeOrderBot (Cardinal.IsRegular.ne_zero Fact.out)
  simp only [trivialCofibrations, cofibrations_eq, weakEquivalences_eq, fibrations_eq,
    ← llp_rlp_J hIW₁ hIW₃ κ hκ, rlp_llp_rlp]
  infer_instance

variable [HasFiniteLimits C] -- TODO: remove this assumption

instance : HasFiniteLimits (CategoryWithSmithStructure hIW₁ hIW₃) :=
  inferInstanceAs (HasFiniteLimits C)

instance : ModelCategory (CategoryWithSmithStructure hIW₁ hIW₃) where
  cm4b := ModelCategory.hasLiftingProperty_of_joyalTrick (by intros; infer_instance)

end CategoryWithSmithStructure

end HomotopicalAlgebra
