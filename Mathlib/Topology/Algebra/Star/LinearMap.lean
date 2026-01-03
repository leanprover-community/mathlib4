/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Intrinsic star operation on `E →L[R] F`

This file defines the star operation on continuous linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

**Note** that in the case of when `E = F` for a Hilbert space, this `star`
is mathematically distinct from the global instance on `E →L[𝕜] E` where
`star := ContinuousLinearMap.adjoint`.
For that reason, the intrinsic star operation is scoped to `IntrinsicStar`.
-/

@[expose] public section

namespace ContinuousLinearMap
variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousStar E] [ContinuousStar F]

open scoped IntrinsicStar

/-- The intrinsic star operation on continuous linear maps defined by
`(star f) x = star (f (star x))`. -/
def intrinsicStar : Star (E →L[R] F) where
  star f := { star f.toLinearMap with
    cont := by
      dsimp [star]
      exact .comp' continuous_star (.comp' f.continuous continuous_star) }

scoped[IntrinsicStar] attribute [instance] ContinuousLinearMap.intrinsicStar

@[simp] theorem intrinsicStar_apply (f : E →L[R] F) (x : E) : star f x = star (f (star x)) := rfl

@[simp] theorem toLinearMap_intrinsicStar (f : E →L[R] F) :
    (star f).toLinearMap = star f.toLinearMap := rfl

theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : E →L[R] F) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp [IsSelfAdjoint, ContinuousLinearMap.ext_iff, star_eq_iff_star_eq, eq_comm (a := f _)]

theorem IntrinsicStar.isSelfAdjoint_toLinearMap_iff (f : E →L[R] F) :
    IsSelfAdjoint f.toLinearMap ↔ IsSelfAdjoint f := by
  simp [isSelfAdjoint_iff_map_star, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

/-- The involutive intrinsic star structure on continuous linear maps. -/
def intrinsicInvolutiveStar : InvolutiveStar (E →L[R] F) where
  star_involutive x := by ext; simp

scoped[IntrinsicStar] attribute [instance] ContinuousLinearMap.intrinsicInvolutiveStar

/-- The intrinsic star additive monoid structure on continuous linear maps. -/
def intrinsicStarAddMonoid [ContinuousAdd F] : StarAddMonoid (E →L[R] F) where
  star_add x y := by ext; simp

scoped[IntrinsicStar] attribute [instance] ContinuousLinearMap.intrinsicStarAddMonoid

theorem intrinsicStar_comp {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : E →L[R] F) (g : G →L[R] E) :
    star (f ∘L g) = star f ∘L star g := by ext; simp

@[simp] theorem intrinsicStar_id : star (ContinuousLinearMap.id R E) = .id R E := by ext; simp
@[simp] theorem intrinsicStar_zero : star (0 : E →L[R] F) = 0 := by ext; simp

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]
  [TopologicalSpace S] [ContinuousStar S]

@[simp] theorem intrinsicStar_toSpanSingleton [ContinuousSMul S E] (a : E) :
    star (toSpanSingleton S a) = toSpanSingleton S (star a) := by ext; simp

theorem intrinsicStar_smulRight [Module S F] [StarModule S F] [ContinuousSMul S F]
    (f : E →L[S] S) (x : F) : star (f.smulRight x) = (star f).smulRight (star x) := by ext; simp

end starAddMonoidSemiring

lemma intrinsicStarModule [SMulCommClass R R F] [ContinuousConstSMul R F] :
    StarModule R (E →L[R] F) where star_smul _ _ := by ext; simp

scoped[IntrinsicStar] attribute [instance] ContinuousLinearMap.intrinsicStarModule

lemma intrinsicStar_eq_comp {R : Type*} [CommSemiring R] [StarRing R] [Module R E] [StarModule R E]
    [Module R F] [StarModule R F] (f : E →L[R] F) :
    star f = (starL R).toContinuousLinearMap.comp (f.comp (starL R).toContinuousLinearMap) := rfl

end ContinuousLinearMap
