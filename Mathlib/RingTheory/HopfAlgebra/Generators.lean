/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Constructing Hopf algebras from algebra generators

This file provides constructors for Hopf algebras given antimultiplicative
antipode data on an algebra-generating set.

## Main declarations

* `HopfAlgebra.ofGenerators` : construct a Hopf algebra from data on a generating set.
* `HopfAlgebra.convMul_id_eq_one_of_adjoin_eq_top` and its left analogue: the
  extension principle promoting pointwise convolution-inverse on generators to a global identity.
-/

public section

namespace HopfAlgebra

open Coalgebra LinearMap WithConv

variable {R A : Type*} [CommSemiring R]

section ExtensionPrinciple

/-! ### Extension principle from algebra generators -/

variable [Semiring A] [Bialgebra R A] {S₀ : A →ₗ[R] A} {s : Set A}

/-- A unital antimultiplicative right convolution inverse of the identity on an
algebra-generating set is one globally. -/
theorem convMul_id_eq_one_of_adjoin_eq_top (hS₀_one : S₀ 1 = 1)
    (hS₀_anti : ∀ x y : A, S₀ (x * y) = S₀ y * S₀ x)
    (hgen : Algebra.adjoin R s = ⊤)
    (h_on_s : ∀ p ∈ s,
      (toConv S₀ * toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p) :
    toConv S₀ * toConv .id = 1 := by
  refine WithConv.ext (ext fun x => ?_)
  refine Algebra.adjoin_induction h_on_s
    (fun r => by simp [hS₀_one, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => ?_) (hgen ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [𝓡a.convMul_apply, 𝓡b.convMul_apply, id_apply, convOne_apply] at ha hb
  rw [convOne_apply]
  calc (toConv S₀ * toConv (.id : A →ₗ[R] A)) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            S₀ (𝓡a.left p * 𝓡b.left q) * (𝓡a.right p * 𝓡b.right q) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum]
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            S₀ (𝓡b.left q) * (S₀ (𝓡a.left p) * 𝓡a.right p) * 𝓡b.right q := by
        simp_rw [hS₀_anti, mul_assoc]
      _ = ∑ q ∈ 𝓡b.index, algebraMap R A (counit a) * S₀ (𝓡b.left q) * 𝓡b.right q := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ha, ← Algebra.commutes]
      _ = algebraMap R A (counit (a * b)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, hb, ← map_mul, ← Bialgebra.counit_mul]

/-- Left analogue of `convMul_id_eq_one_of_adjoin_eq_top`. -/
theorem id_convMul_eq_one_of_adjoin_eq_top (hS₀_one : S₀ 1 = 1)
    (hS₀_anti : ∀ x y : A, S₀ (x * y) = S₀ y * S₀ x)
    (hgen : Algebra.adjoin R s = ⊤)
    (h_on_s : ∀ p ∈ s,
      (toConv (.id : A →ₗ[R] A) * toConv S₀) p = (1 : WithConv (A →ₗ[R] A)) p) :
    toConv .id * toConv S₀ = 1 := by
  refine WithConv.ext (ext fun x => ?_)
  refine Algebra.adjoin_induction h_on_s
    (fun r => by simp [hS₀_one, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => ?_) (hgen ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [𝓡a.convMul_apply, 𝓡b.convMul_apply, id_apply, convOne_apply] at ha hb
  rw [convOne_apply]
  calc (toConv (.id : A →ₗ[R] A) * toConv S₀) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            (𝓡a.left p * 𝓡b.left q) * S₀ (𝓡a.right p * 𝓡b.right q) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum]
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            𝓡a.left p * (𝓡b.left q * S₀ (𝓡b.right q)) * S₀ (𝓡a.right p) := by
        simp_rw [hS₀_anti, mul_assoc]
      _ = ∑ p ∈ 𝓡a.index,
            algebraMap R A (counit b) * 𝓡a.left p * S₀ (𝓡a.right p) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hb, ← Algebra.commutes]
      _ = algebraMap R A (counit (a * b)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ha, ← map_mul, mul_comm (counit b),
          ← Bialgebra.counit_mul]

variable (S₀) in
/-- Upgrade a bialgebra to a Hopf algebra from a unital antimultiplicative candidate antipode
that is a two-sided convolution inverse of the identity pointwise on an algebra-generating
set. -/
noncomputable abbrev ofGenerators (hS₀_one : S₀ 1 = 1)
    (hS₀_anti : ∀ x y : A, S₀ (x * y) = S₀ y * S₀ x)
    (hgen : Algebra.adjoin R s = ⊤)
    (hl : ∀ p ∈ s, (toConv S₀ * toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p)
    (hr : ∀ p ∈ s, (toConv (.id : A →ₗ[R] A) * toConv S₀) p = (1 : WithConv (A →ₗ[R] A)) p) :
    HopfAlgebra R A :=
  ofConvInverse S₀
    (convMul_id_eq_one_of_adjoin_eq_top hS₀_one hS₀_anti hgen hl)
    (id_convMul_eq_one_of_adjoin_eq_top hS₀_one hS₀_anti hgen hr)

end ExtensionPrinciple

end HopfAlgebra
