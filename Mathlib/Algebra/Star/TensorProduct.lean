/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Star.Module

/-!
# The star structure on tensor products

This file defines the `Star` structure on tensor products. This also
defines the `StarAddMonoid` and `StarModule` instances for tensor products.
-/

namespace TensorProduct
variable {R A B : Type*}
  [CommSemiring R] [StarRing R]
  [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]
  [AddCommMonoid B] [StarAddMonoid B] [Module R B] [StarModule R B]

open scoped TensorProduct

instance : Star (A ⊗[R] B) where
  star x := congr (starLinearEquiv R) (starLinearEquiv R) x

@[simp]
theorem star_tmul (x : A) (y : B) : star (x ⊗ₜ[R] y) = star x ⊗ₜ[R] star y := rfl

noncomputable instance : InvolutiveStar (A ⊗[R] B) where
  star_involutive x := by
    simp_rw [star]
    rw [congr_congr]
    convert congr($congr_refl_refl x) <;> ext <;> simp

noncomputable instance : StarAddMonoid (A ⊗[R] B) where
  star_add := LinearMap.map_add _

instance : StarModule R (A ⊗[R] B) where
  star_smul := LinearMap.map_smulₛₗ _

theorem _root_.starLinearEquiv_tensor :
    starLinearEquiv R (A := A ⊗[R] B) = congr (starLinearEquiv R) (starLinearEquiv R) := rfl

end TensorProduct

namespace LinearMap
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

open scoped IntrinsicStar

theorem _root_.TensorProduct.intrinsicStar_map (f : E →ₗ[R] F) (g : G →ₗ[R] H) :
    star (TensorProduct.map f g) = TensorProduct.map (star f) (star g) :=
  TensorProduct.ext' fun _ _ ↦ by simp

theorem intrinsicStar_lTensor (f : F →ₗ[R] G) : star (lTensor E f) = lTensor E (star f) := by
  simp [lTensor, TensorProduct.intrinsicStar_map]

theorem intrinsicStar_rTensor (f : E →ₗ[R] F) : star (rTensor G f) = rTensor G (star f) := by
  simp [rTensor, TensorProduct.intrinsicStar_map]

section NonUnitalNonAssocSemiring
variable {E : Type*} [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E]
  [StarModule R E] [SMulCommClass R E E] [IsScalarTower R E E]

theorem intrinsicStar_mul' : star (mul' R E) = mul' R E ∘ₗ TensorProduct.comm R E E :=
  TensorProduct.ext' fun _ _ ↦ by simp

end NonUnitalNonAssocSemiring

end LinearMap
