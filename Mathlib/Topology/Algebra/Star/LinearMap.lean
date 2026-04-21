/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Topology.Algebra.Module.Star

/-! # Intrinsic star operation on continuous linear maps

This file defines the star operation on continuous linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

This is the continuous version of the intrinsic star on linear maps (see
`Mathlib/Algebra/Star/LinearMap.lean`).

## Implementation notes

Because there is a global `star` instance on `H →L[𝕜] H` (defined as the linear map adjoint on
Hilbert spaces), which is mathematically distinct from this `star`, we provide
this instance on `WithConv (E →L[R] F)`. -/

@[expose] public section

namespace ContinuousLinearMap
variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousStar E] [ContinuousStar F]

open WithConv

/-- The intrinsic star operation on continuous linear maps defined by
`(star f) x = star (f (star x))`. -/
instance intrinsicStar : Star (WithConv (E →L[R] F)) where star f := toConv <|
  { (star (toConv f.ofConv.toLinearMap)).ofConv with
    cont := by
      dsimp [star]
      exact .comp' continuous_star (.comp' f.ofConv.continuous continuous_star) }

@[simp] theorem intrinsicStar_apply (f : WithConv (E →L[R] F)) (x : E) :
    star f x = star (f (star x)) := rfl

@[simp] theorem toLinearMap_intrinsicStar (f : WithConv (E →L[R] F)) :
    (star f).ofConv.toLinearMap = (star (toConv f.ofConv.toLinearMap)).ofConv := rfl

theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E →L[R] F)) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp [IsSelfAdjoint, WithConv.ext_iff, ContinuousLinearMap.ext_iff, star_eq_iff_star_eq,
    eq_comm (a := f _)]

theorem IntrinsicStar.isSelfAdjoint_toLinearMap_iff (f : WithConv (E →L[R] F)) :
    IsSelfAdjoint (toConv f.ofConv.toLinearMap) ↔ IsSelfAdjoint f := by
  simp [isSelfAdjoint_iff_map_star, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

/-- The involutive intrinsic star structure on continuous linear maps. -/
instance intrinsicInvolutiveStar : InvolutiveStar (WithConv (E →L[R] F)) where
  star_involutive x := by ext; simp

/-- The intrinsic star additive monoid structure on continuous linear maps. -/
instance intrinsicStarAddMonoid [ContinuousAdd F] : StarAddMonoid (WithConv (E →L[R] F)) where
  star_add x y := by ext; simp

theorem intrinsicStar_comp {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : WithConv (E →L[R] F))
    (g : WithConv (G →L[R] E)) :
    star (toConv (f.ofConv ∘L g.ofConv)) = toConv ((star f).ofConv ∘L (star g).ofConv) := by
  ext; simp

theorem intrinsicStar_comp' {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : E →L[R] F) (g : G →L[R] E) :
    star (toConv (f ∘L g)) = toConv ((star (toConv f)).ofConv ∘L (star (toConv g)).ofConv) := by
  ext; simp

@[simp] theorem intrinsicStar_id :
    star (toConv (ContinuousLinearMap.id R E)) = toConv (.id R E) := by ext; simp
@[simp] theorem intrinsicStar_zero : star (toConv (0 : E →L[R] F)) = toConv 0 := by ext; simp

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]
  [TopologicalSpace S] [ContinuousStar S]

@[simp] theorem intrinsicStar_toSpanSingleton [ContinuousSMul S E] (a : E) :
    star (toConv (toSpanSingleton S a)) = toConv (toSpanSingleton S (star a)) := by ext; simp

theorem intrinsicStar_smulRight [Module S F] [StarModule S F] [ContinuousSMul S F]
    (f : WithConv (E →L[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

instance intrinsicStarModule [SMulCommClass R R F] [ContinuousConstSMul R F] :
    StarModule R (WithConv (E →L[R] F)) where star_smul _ _ := by ext; simp

lemma intrinsicStar_eq_comp {R : Type*} [CommSemiring R] [StarRing R] [Module R E] [StarModule R E]
    [Module R F] [StarModule R F] (f : WithConv (E →L[R] F)) :
    star f = toConv
      ((starL R).toContinuousLinearMap.comp (f.ofConv.comp (starL R).toContinuousLinearMap)) := rfl

end ContinuousLinearMap
