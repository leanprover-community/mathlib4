/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Filtered.Countable
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered

import Mathlib.Logic.Equiv.List

/-!
# Constructing countable limits from finite and sequential limits

Sequential limits suffice for limits over countable cofiltered categories. Together with finite
limits, they give all countable limits: first construct countable products as limits of finite
subproducts, then construct arbitrary countable limits from products and equalizers.

We also prove the dual statements for colimits.
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- Sequential limits give limits over all countable cofiltered categories. -/
theorem hasCofilteredCountableLimits_of_hasSequentialLimits [HasLimitsOfShape ℕᵒᵖ C]
    (J : Type*) [Category* J] [IsCofiltered J] [CountableCategory J] : HasLimitsOfShape J C := by
  obtain ⟨F, _⟩ := CategoryTheory.IsCofiltered.exists_initial_nat J
  exact Functor.Initial.hasLimitsOfShape_of_initial F

/-- Sequential colimits give colimits over all countable filtered categories. -/
theorem hasFilteredCountableColimits_of_hasSequentialColimits [HasColimitsOfShape ℕ C]
    (J : Type*) [Category* J] [IsFiltered J] [CountableCategory J] : HasColimitsOfShape J C := by
  obtain ⟨F, _⟩ := CategoryTheory.IsFiltered.exists_final_nat J
  exact Functor.Final.hasColimitsOfShape_of_final F

/-- Finite products and sequential limits suffice to construct countable products. -/
theorem hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits
    [HasFiniteProducts C] [HasLimitsOfShape ℕᵒᵖ C] : HasCountableProducts C where
  out J _ := by
    have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      hasCofilteredCountableLimits_of_hasSequentialLimits _
    exact ⟨fun F ↦ HasLimit.mk (ProductsFromFiniteCofiltered.liftToFinsetLimitCone F)⟩

/-- Finite coproducts and sequential colimits suffice to construct countable coproducts. -/
theorem hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits
    [HasFiniteCoproducts C] [HasColimitsOfShape ℕ C] : HasCountableCoproducts C where
  out J _ := by
    have : HasColimitsOfShape (Finset (Discrete J)) C :=
      hasFilteredCountableColimits_of_hasSequentialColimits _
    exact ⟨fun F ↦ HasColimit.mk (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone F)⟩

/-- Countable products and equalizers suffice to construct countable limits. -/
theorem hasCountableLimits_of_hasEqualizers_and_countableProducts
    [HasEqualizers C] [HasCountableProducts C] : HasCountableLimits C where
  out _ := ⟨fun F ↦ hasLimit_of_equalizer_and_product F⟩

/-- Countable coproducts and coequalizers suffice to construct countable colimits. -/
theorem hasCountableColimits_of_hasCoequalizers_and_countableCoproducts
    [HasCoequalizers C] [HasCountableCoproducts C] : HasCountableColimits C where
  out _ := ⟨fun F ↦ hasColimit_of_coequalizer_and_coproduct F⟩

/-- Finite limits and sequential limits suffice to construct countable limits. -/
theorem hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits
    [HasFiniteLimits C] [HasLimitsOfShape ℕᵒᵖ C] : HasCountableLimits C := by
  have : HasCountableProducts C :=
    hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits
  exact hasCountableLimits_of_hasEqualizers_and_countableProducts

/-- Finite colimits and sequential colimits suffice to construct countable colimits. -/
theorem hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits
    [HasFiniteColimits C] [HasColimitsOfShape ℕ C] : HasCountableColimits C := by
  have : HasCountableCoproducts C :=
    hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits
  exact hasCountableColimits_of_hasCoequalizers_and_countableCoproducts

end CategoryTheory.Limits
