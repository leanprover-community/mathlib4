/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Constructing Hopf algebras from algebra generators

This file provides an extension principle to upgrade a bialgebra to a Hopf algebra given
antimultiplicative antipode data on generators.

## Main definitions

* `HopfAlgebra.ofGenerators`: construct a Hopf algebra from data on a generating set.

## Main results

* `LinearMap.convMul_id_eq_one_of_adjoin_eq_top` and
  `LinearMap.id_convMul_eq_one_of_adjoin_eq_top`: a pointwise one-sided convolution inverse of
  the identity on generators is a global one.
-/

public section

open Algebra Coalgebra LinearMap MulOpposite WithConv

variable {R A : Type*} [CommSemiring R]

namespace LinearMap

section ExtensionPrinciple

/-! ### Extension principle from algebra generators -/

variable [Semiring A] [Bialgebra R A] {g : A →ₗ[R] A} {s : Set A}

/-- If a unital antimultiplicative map `g` is a left convolution inverse of the identity
pointwise on an algebra-generating set, then `toConv g * toConv id = 1`. -/
theorem convMul_id_eq_one_of_adjoin_eq_top
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (adjoin_eq_top : adjoin R s = ⊤)
    (g_convMul_id : ∀ p ∈ s,
      (toConv g * toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p) :
    toConv g * toConv id = 1 := by
  ext x; refine adjoin_le
    (S := (eqLocus (toConv g * toConv (.id : A →ₗ[R] A)).ofConv (ofConv 1)).toSubalgebra ?_
      fun a b ha hb ↦ ?_)
    g_convMul_id (adjoin_eq_top.ge mem_top)
  · simp [g_one, TensorProduct.one_def]
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [mem_eqLocus, 𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply, id_apply] at ha hb ⊢
  calc (toConv g * toConv (.id : A →ₗ[R] A)) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            g (𝓡b.left q) * (g (𝓡a.left p) * 𝓡a.right p) * 𝓡b.right q := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, g_mul, mul_assoc]
      _ = algebraMap R A (counit (a * b)) := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ha, ← commutes]
        simp_rw [mul_assoc, ← Finset.mul_sum, hb, ← map_mul, ← Bialgebra.counit_mul]

/-- If a unital antimultiplicative map `g` is a right convolution inverse of the identity
pointwise on an algebra-generating set, then `toConv id * toConv g = 1`. -/
theorem id_convMul_eq_one_of_adjoin_eq_top
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (adjoin_eq_top : adjoin R s = ⊤)
    (id_convMul_g : ∀ p ∈ s,
      (toConv (.id : A →ₗ[R] A) * toConv g) p = (1 : WithConv (A →ₗ[R] A)) p) :
    toConv id * toConv g = 1 := by
  ext x; refine adjoin_le
    (S := (eqLocus (toConv (.id : A →ₗ[R] A) * toConv g).ofConv (ofConv 1)).toSubalgebra ?_
      fun a b ha hb ↦ ?_)
    id_convMul_g (adjoin_eq_top.ge mem_top)
  · simp [g_one, TensorProduct.one_def]
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [mem_eqLocus, 𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply, id_apply] at ha hb ⊢
  calc (toConv (.id : A →ₗ[R] A) * toConv g) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            𝓡a.left p * (𝓡b.left q * g (𝓡b.right q)) * g (𝓡a.right p) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, g_mul, mul_assoc]
      _ = algebraMap R A (counit (a * b)) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hb, ← commutes]
        simp_rw [mul_assoc, ← Finset.mul_sum, ha, ← map_mul, mul_comm (counit b),
          ← Bialgebra.counit_mul]

end ExtensionPrinciple

end LinearMap

namespace HopfAlgebra

section Construction
variable [Semiring A] [Bialgebra R A] {s : Set A}

/-- Build a Hopf algebra structure on a bialgebra `A` from an algebra homomorphism into
`Aᵐᵒᵖ` that is a two-sided convolution inverse of the identity at every element of an
algebra-generating set. -/
noncomputable abbrev ofGenerators (S : A →ₐ[R] Aᵐᵒᵖ) (adjoin_eq_top : adjoin R s = ⊤)
    (S_convMul_id : ∀ p ∈ s,
      (toConv ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) *
        toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p)
    (id_convMul_S : ∀ p ∈ s,
      (toConv (.id : A →ₗ[R] A) *
        toConv ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)) p =
        (1 : WithConv (A →ₗ[R] A)) p) :
    HopfAlgebra R A :=
  ofConvInverse ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)
    (convMul_id_eq_one_of_adjoin_eq_top (by simp) (fun _ _ ↦ by simp) adjoin_eq_top
      S_convMul_id)
    (id_convMul_eq_one_of_adjoin_eq_top (by simp) (fun _ _ ↦ by simp) adjoin_eq_top
      id_convMul_S)

end Construction

end HopfAlgebra
