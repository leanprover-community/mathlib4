/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.TensorProduct

/-!
# Intrinsic star operation on `E →ₗ[R] F`

This file defines the star operation on linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

**Note** that in the case of when `E = F` for a finite-dimensional Hilbert space, this `star`
is mathematically distinct from the global instance on `E →ₗ[𝕜] E` where
`star := LinearMap.adjoint`.
For that reason, the intrinsic star operation is scoped to `IntrinsicStar`.
-/

namespace LinearMap
variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

/-- The intrinsic star operation on linear maps `E →ₗ F` defined by
`(star f) x = star (f (star x))`. -/
def intrinsicStar : Star (E →ₗ[R] F) where
  star f :=
  { toFun x := star (f (star x))
    map_add' _ _ := by simp
    map_smul' _ _ := by simp }

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicStar

open scoped IntrinsicStar

@[simp] theorem intrinsicStar_apply (f : E →ₗ[R] F) (x : E) : (star f) x = star (f (star x)) := rfl

/-- The involutive intrinsic star structure on linear maps. -/
def intrinsicInvolutiveStar : InvolutiveStar (E →ₗ[R] F) where
  star_involutive x := by ext; simp

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicInvolutiveStar

/-- The intrinsic star additive monoid structure on linear maps. -/
def intrinsicStarAddMonoid : StarAddMonoid (E →ₗ[R] F) where
  star_add x y := by ext; simp

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicStarAddMonoid

theorem isSelfAdjoint_iff_map_star (f : E →ₗ[R] F) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, LinearMap.ext_iff, intrinsicStar_apply, star_eq_iff_star_eq, eq_comm]

@[simp]
protected theorem _root_.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} : IsSelfAdjoint (f : E →ₗ[R] F) :=
  isSelfAdjoint_iff_map_star _ |>.mpr (map_star f)

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

theorem intrinsicStar_comp (f : E →ₗ[R] F) (g : G →ₗ[R] E) :
    star (f ∘ₗ g) = star f ∘ₗ star g := by ext; simp

@[simp] theorem intrinsicStar_id : star (LinearMap.id (R := R) (M := E)) = LinearMap.id := by
  ext; simp
@[simp] theorem intrinsicStar_zero : star (0 : E →ₗ[R] F) = 0 := by ext; simp

section NonUnitalNonAssocSemiring
variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

theorem intrinsicStar_mulLeft (x : E) : star (mulLeft R x) = mulRight R (star x) := by ext; simp

theorem intrinsicStar_mulRight (x : E) : star (mulRight R x) = mulLeft R (star x) := by
  rw [star_eq_iff_star_eq, intrinsicStar_mulLeft, star_star]

theorem intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] :
    star (mul' R' E) = mul' R' E ∘ₗ TensorProduct.comm R' E E :=
  TensorProduct.ext' fun _ _ ↦ by simp

end NonUnitalNonAssocSemiring

variable [SMulCommClass R R F] in
lemma intrinsicStarModule : StarModule R (E →ₗ[R] F) where
  star_smul _ _ := by ext; simp

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicStarModule

section TensorProduct
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

theorem _root_.TensorProduct.intrinsicStar_map (f : E →ₗ[R] F) (g : G →ₗ[R] H) :
    star (TensorProduct.map f g) = TensorProduct.map (star f) (star g) :=
  TensorProduct.ext' fun _ _ ↦ by simp

theorem intrinsicStar_lTensor (f : F →ₗ[R] G) : star (lTensor E f) = lTensor E (star f) := by
  simp [lTensor, TensorProduct.intrinsicStar_map]

theorem intrinsicStar_rTensor (f : E →ₗ[R] F) : star (rTensor G f) = rTensor G (star f) := by
  simp [rTensor, TensorProduct.intrinsicStar_map]

end TensorProduct

end LinearMap
