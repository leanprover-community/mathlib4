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

This file provides a constructor for Hopf algebras given antimultiplicative
antipode data on an algebra-generating set, via an extension principle for
pointwise convolution inverses of multiplicative maps.

## Main declarations

* `HopfAlgebra.ofGenerators` : construct a Hopf algebra from data on a generating set.
* `HopfAlgebra.convMul_eq_one_of_adjoin_eq_top_left` and
  `convMul_eq_one_of_adjoin_eq_top_right`: the extension principle promoting a pointwise
  one-sided convolution inverse of a multiplicative map on generators to a global one.
-/

public section

namespace HopfAlgebra

open Coalgebra LinearMap WithConv

variable {R A B : Type*} [CommSemiring R]

section ExtensionPrinciple

/-! ### Extension principle from algebra generators -/

variable [Semiring A] [Bialgebra R A] [Semiring B] [Algebra R B]
  {g f : A →ₗ[R] B} {s : Set A}

/-- If a unital antimultiplicative map `g` and a unital multiplicative map `f` satisfy
`toConv g * toConv f = 1` pointwise on an algebra-generating set, then they do so globally:
a left convolution inverse on generators is a left convolution inverse. -/
theorem convMul_eq_one_of_adjoin_eq_top_left
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (f_one : f 1 = 1) (f_mul : ∀ x y, f (x * y) = f x * f y)
    (adjoin_eq_top : Algebra.adjoin R s = ⊤)
    (g_convMul_f : ∀ p ∈ s, (toConv g * toConv f) p = (1 : WithConv (A →ₗ[R] B)) p) :
    toConv g * toConv f = 1 := by
  refine WithConv.ext (ext fun x => ?_)
  refine Algebra.adjoin_induction g_convMul_f
    (fun r => by simp [g_one, f_one, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => ?_) (adjoin_eq_top ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply] at ha hb
  rw [convOne_apply]
  calc (toConv g * toConv f) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            g (𝓡a.left p * 𝓡b.left q) * f (𝓡a.right p * 𝓡b.right q) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum]
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            g (𝓡b.left q) * (g (𝓡a.left p) * f (𝓡a.right p)) * f (𝓡b.right q) := by
        simp_rw [g_mul, f_mul, mul_assoc]
      _ = ∑ q ∈ 𝓡b.index, algebraMap R B (counit a) * g (𝓡b.left q) * f (𝓡b.right q) := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ha, ← Algebra.commutes]
      _ = algebraMap R B (counit (a * b)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, hb, ← map_mul, ← Bialgebra.counit_mul]

/-- Analogue of `convMul_eq_one_of_adjoin_eq_top_left` for `toConv f * toConv g = 1`:
a right convolution inverse on generators is a right convolution inverse. -/
theorem convMul_eq_one_of_adjoin_eq_top_right
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (f_one : f 1 = 1) (f_mul : ∀ x y, f (x * y) = f x * f y)
    (adjoin_eq_top : Algebra.adjoin R s = ⊤)
    (f_convMul_g : ∀ p ∈ s, (toConv f * toConv g) p = (1 : WithConv (A →ₗ[R] B)) p) :
    toConv f * toConv g = 1 := by
  refine WithConv.ext (ext fun x => ?_)
  refine Algebra.adjoin_induction f_convMul_g
    (fun r => by simp [g_one, f_one, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => ?_) (adjoin_eq_top ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply] at ha hb
  rw [convOne_apply]
  calc (toConv f * toConv g) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            f (𝓡a.left p * 𝓡b.left q) * g (𝓡a.right p * 𝓡b.right q) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum]
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            f (𝓡a.left p) * (f (𝓡b.left q) * g (𝓡b.right q)) * g (𝓡a.right p) := by
        simp_rw [g_mul, f_mul, mul_assoc]
      _ = ∑ p ∈ 𝓡a.index, algebraMap R B (counit b) * f (𝓡a.left p) * g (𝓡a.right p) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hb, ← Algebra.commutes]
      _ = algebraMap R B (counit (a * b)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ha, ← map_mul, mul_comm (counit b),
          ← Bialgebra.counit_mul]

end ExtensionPrinciple

variable [Semiring A] [Bialgebra R A] {S₀ : A →ₗ[R] A} {s : Set A}

variable (S₀) in
/-- Upgrade a bialgebra to a Hopf algebra from a unital antimultiplicative candidate antipode
that is a two-sided convolution inverse of the identity pointwise on an algebra-generating
set. -/
noncomputable abbrev ofGenerators (S₀_one : S₀ 1 = 1) (S₀_mul : ∀ x y, S₀ (x * y) = S₀ y * S₀ x)
    (adjoin_eq_top : Algebra.adjoin R s = ⊤)
    (S₀_convMul_id : ∀ p ∈ s,
      (toConv S₀ * toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p)
    (id_convMul_S₀ : ∀ p ∈ s,
      (toConv (.id : A →ₗ[R] A) * toConv S₀) p = (1 : WithConv (A →ₗ[R] A)) p) :
    HopfAlgebra R A :=
  ofConvInverse S₀
    (convMul_eq_one_of_adjoin_eq_top_left S₀_one S₀_mul rfl (fun _ _ => rfl)
      adjoin_eq_top S₀_convMul_id)
    (convMul_eq_one_of_adjoin_eq_top_right S₀_one S₀_mul rfl (fun _ _ => rfl)
      adjoin_eq_top id_convMul_S₀)

end HopfAlgebra
