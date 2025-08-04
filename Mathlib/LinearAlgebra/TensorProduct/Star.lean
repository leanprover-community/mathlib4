/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Star.Module

/-!

This file defines the `Star` structure on tensor products. This also
defines the `StarAddMonoid` and `StarModule` instances for tensor products.

-/

namespace TensorProduct

open scoped TensorProduct

variable {R A B : Type*} [CommSemiring R]
  [StarRing R] [AddCommMonoid A] [AddCommMonoid B] [StarAddMonoid A]
  [StarAddMonoid B] [Module R A] [Module R B] [StarModule R A] [StarModule R B]

instance : Star (A ⊗[R] B) where
  star x := mapₛₗ (starLinearEquiv R).toLinearMap (starLinearEquiv R).toLinearMap x

@[simp]
theorem star_tmul (x : A) (y : B) :
    star (x ⊗ₜ[R] y) = star x ⊗ₜ[R] star y :=
  rfl

noncomputable instance : InvolutiveStar (A ⊗[R] B) where
  star_involutive x := by
    nth_rw 2 [← LinearMap.id_apply (R:=R) x]
    revert x
    simp_rw [star, ← LinearMap.comp_apply, ← LinearMap.ext_iff]
    apply TensorProduct.ext'
    simp

noncomputable instance : StarAddMonoid (A ⊗[R] B) where
  star_add _ _ := by simp [star]

instance : StarModule R (A ⊗[R] B) where
  star_smul r α := by simp [star]; rfl

end TensorProduct
