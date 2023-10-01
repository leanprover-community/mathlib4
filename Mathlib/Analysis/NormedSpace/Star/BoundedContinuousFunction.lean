/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.NormedSpace.Star.GelfandDuality
import Mathlib.Topology.StoneCech
import Mathlib.Topology.ContinuousFunction.Ideals

/-!
# StoneCech

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open WeakDual
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

variable (X : Type*) [TopologicalSpace X]

def evalCharacterSpace (x : X) : characterSpace ℂ (X →ᵇ ℂ) :=
  ⟨evalClm ℂ x, by
    rw [CharacterSpace.eq_set_map_one_map_mul]
    exact ⟨rfl, fun _ _ ↦ rfl⟩⟩

theorem continuous_evalCharacterSpace :
    Continuous (evalCharacterSpace X) :=
  continuous_induced_rng.mpr <| continuous_of_continuous_eval fun f ↦ f.continuous

#check ContinuousMap.compRightAlgHom

noncomputable
def foo (X : Type*) [TopologicalSpace X] : characterSpace ℂ (X →ᵇ ℂ) ≃ₜ StoneCech X where
  toFun :=
    (CharacterSpace.homeoEval (StoneCech X) ℂ).symm ∘ CharacterSpace.compContinuousMap
      (StarAlgHom.comp (compContinuousStarAlgHom ) <| ContinuousMap.starAlgEquivBoundedOfCompact (StoneCech X) ℂ ℂ) -- BoundedContinuousFunction.starAlgEquivBoundedOfCompact
  invFun := stoneCechExtend (continuous_evalCharacterSpace X)
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := continuous_stoneCechExtend (continuous_evalCharacterSpace X)

end BoundedContinuousFunction
