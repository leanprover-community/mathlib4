/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# GNS Construction for C*-algebras

## Main definitions

## Main statements

## Notation

## Implementation details

## References

## Tags

-/

open ComplexOrder RCLike

variable {𝕜 A B : Type*}
variable [RCLike 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A] [StarRing A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NormedRing B] [NormedAlgebra 𝕜 B] [StarRing B]
variable [PartialOrder B] [StarOrderedRing B]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace ContinuousLinearMap

lemma map_star_of_monotone (φ : A →L[𝕜] B) (hφ : Monotone φ) (x : A) :
    φ (star x) = star (φ x) :=
  sorry -- needs splitting up into four parts, probably needs some API to be easy

structure hasVectorTriple (φ : A →L[𝕜] 𝕜) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (π : A →⋆ₐ[𝕜] H →L[𝕜] H) (ξ : H) : Prop where
  eq_inner : ∀ a : A, φ a = ⟪ξ, π a ξ⟫

structure hasGNSTriple (φ : A →L[𝕜] 𝕜) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (π : A →⋆ₐ[𝕜] H →L[𝕜] H) (ξ : H)
    extends φ.hasVectorTriple H π ξ : Prop where
  cyclic : DenseRange (fun a ↦ π a ξ)

set_option linter.unusedVariables false in
def GNSPreSpace (φ : A →L[𝕜] 𝕜) (hφ : Monotone φ) : Type _ := A

variable (φ : A →L[𝕜] 𝕜) (hφ : Monotone φ)

instance : AddCommGroup (GNSPreSpace φ hφ) := inferInstanceAs <| AddCommGroup A
instance : Mul (GNSPreSpace φ hφ) := inferInstanceAs <| Mul A
instance : Star (GNSPreSpace φ hφ) := inferInstanceAs <| Star A
instance : Module 𝕜 (GNSPreSpace φ hφ) := inferInstanceAs <| Module 𝕜 A

def GNSPreSpace.core : InnerProductSpace.Core 𝕜 (GNSPreSpace φ hφ) where
  inner a b := φ (star a * b)
  conj_symm a b := by simp [starRingEnd, ← map_star_of_monotone φ hφ]
  nonneg_re x := sorry -- API lacking: monotonicity of `re`...
  definite := sorry
  add_left := sorry
  smul_left := sorry

end ContinuousLinearMap
