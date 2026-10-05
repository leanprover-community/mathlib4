/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import Mathlib.Basic.Countable.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.Logic.Equiv.List

/-!
# Constructing countable limits from finite limits and sequential limits

A category with finite limits and sequential limits (limits of shape `ℕᵒᵖ`) has countable limits,
and dually a category with finite colimits and sequential colimits (colimits of shape `ℕ`) has
countable colimits. These are the countable versions of `has_limits_of_finite_and_cofiltered` and
`has_colimits_of_finite_and_filtered`.

A countable coproduct is the colimit of the coproducts over the finite subsets of its index type.
These subsets form a countable directed set, which receives a final functor from `ℕ`
(`IsFiltered.sequentialFunctor_final`), so that this colimit is a sequential colimit. A countable
colimit is a coequalizer of two maps between countable coproducts.

## Main results

* `hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits`
* `hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits`
* `hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits`
* `hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits`
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- A category with finite coproducts and sequential colimits has countable coproducts. -/
theorem hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits
    [HasFiniteCoproducts C] [HasColimitsOfShape ℕ C] : HasCountableCoproducts C where
  out α _ :=
    have : HasColimitsOfShape (Finset (Discrete α)) C :=
      Functor.Final.hasColimitsOfShape_of_final (IsFiltered.sequentialFunctor _)
    ⟨fun F => HasColimit.mk (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone F)⟩

/-- A category with finite colimits and sequential colimits has countable colimits. -/
theorem hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits
    [HasFiniteColimits C] [HasColimitsOfShape ℕ C] : HasCountableColimits C where
  out _ _ _ :=
    have := hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits (C := C)
    ⟨fun F => hasColimit_of_coequalizer_and_coproduct F⟩

/-- A category with finite products and sequential limits has countable products. -/
theorem hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits
    [HasFiniteProducts C] [HasLimitsOfShape ℕᵒᵖ C] : HasCountableProducts C where
  out α _ :=
    have : HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial (IsFiltered.sequentialFunctor _).op
    ⟨fun F => HasLimit.mk (ProductsFromFiniteCofiltered.liftToFinsetLimitCone F)⟩

/-- A category with finite limits and sequential limits has countable limits. -/
theorem hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits
    [HasFiniteLimits C] [HasLimitsOfShape ℕᵒᵖ C] : HasCountableLimits C where
  out _ _ _ :=
    have := hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits (C := C)
    ⟨fun F => hasLimit_of_equalizer_and_product F⟩

end CategoryTheory.Limits
