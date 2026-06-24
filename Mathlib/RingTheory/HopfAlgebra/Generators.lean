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

* `HopfAlgebra.ofGenerators` : construct a Hopf algebra from data on a generating set.

## Main results

* `HopfAlgebra.convMul_eq_one_of_adjoin_eq_top_left` and
  `HopfAlgebra.convMul_eq_one_of_adjoin_eq_top_right`: a pointwise one-sided convolution inverse of
  a multiplicative map on generators is a global one.
* `HopfAlgebra.eq_antipode_of_convMul_id_eq_one` : a left convolution inverse of `id` is the
  antipode.
* `HopfAlgebra.eq_antipode_of_adjoin_eq_top` : a left convolution inverse of `id` on a generating
  set is the antipode.
-/

public section

namespace HopfAlgebra

open Algebra Coalgebra LinearMap WithConv

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
    (adjoin_eq_top : adjoin R s = ⊤)
    (g_convMul_f : ∀ p ∈ s, (toConv g * toConv f) p = (1 : WithConv (A →ₗ[R] B)) p) :
    toConv g * toConv f = 1 := by
  ext x; refine adjoin_le
    (S := (eqLocus (toConv g * toConv f).ofConv (ofConv 1)).toSubalgebra ?_ fun a b ha hb => ?_)
    g_convMul_f (adjoin_eq_top ▸ mem_top : x ∈ adjoin R s)
  · simp [g_one, f_one, TensorProduct.one_def]
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [mem_eqLocus, 𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply] at ha hb ⊢
  calc (toConv g * toConv f) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            g (𝓡b.left q) * (g (𝓡a.left p) * f (𝓡a.right p)) * f (𝓡b.right q) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, g_mul, f_mul, mul_assoc]
      _ = ∑ q ∈ 𝓡b.index, algebraMap R B (counit a) * g (𝓡b.left q) * f (𝓡b.right q) := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ha, ← commutes]
      _ = algebraMap R B (counit (a * b)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, hb, ← map_mul, ← Bialgebra.counit_mul]

/-- Analogue of `convMul_eq_one_of_adjoin_eq_top_left` for `toConv f * toConv g = 1`:
a right convolution inverse on generators is a right convolution inverse. -/
theorem convMul_eq_one_of_adjoin_eq_top_right
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (f_one : f 1 = 1) (f_mul : ∀ x y, f (x * y) = f x * f y)
    (adjoin_eq_top : adjoin R s = ⊤)
    (f_convMul_g : ∀ p ∈ s, (toConv f * toConv g) p = (1 : WithConv (A →ₗ[R] B)) p) :
    toConv f * toConv g = 1 := by
  ext x; refine adjoin_le
    (S := (eqLocus (toConv f * toConv g).ofConv (ofConv 1)).toSubalgebra ?_ fun a b ha hb => ?_)
    f_convMul_g (adjoin_eq_top ▸ mem_top : x ∈ adjoin R s)
  · simp [g_one, f_one, TensorProduct.one_def]
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [mem_eqLocus, 𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply] at ha hb ⊢
  calc (toConv f * toConv g) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            f (𝓡a.left p) * (f (𝓡b.left q) * g (𝓡b.right q)) * g (𝓡a.right p) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, g_mul, f_mul, mul_assoc]
      _ = ∑ p ∈ 𝓡a.index, algebraMap R B (counit b) * f (𝓡a.left p) * g (𝓡a.right p) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hb, ← commutes]
      _ = algebraMap R B (counit (a * b)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ha, ← map_mul, mul_comm (counit b),
          ← Bialgebra.counit_mul]

end ExtensionPrinciple

section Construction
variable [Semiring A] [Bialgebra R A] {S₀ : A →ₗ[R] A} {s : Set A}

variable (S₀) in
/-- Upgrade a bialgebra to a Hopf algebra from a unital antimultiplicative candidate antipode
that is a two-sided convolution inverse of the identity pointwise on an algebra-generating
set. -/
noncomputable abbrev ofGenerators (S₀_one : S₀ 1 = 1) (S₀_mul : ∀ x y, S₀ (x * y) = S₀ y * S₀ x)
    (adjoin_eq_top : adjoin R s = ⊤)
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

end Construction

section Uniqueness
variable [Semiring A] [HopfAlgebra R A] {S₀ : A →ₗ[R] A} {s : Set A}

/-- A left convolution inverse of the identity is the antipode. -/
theorem eq_antipode_of_convMul_id_eq_one (h : toConv S₀ * toConv LinearMap.id = 1) :
    S₀ = antipode R :=
  toConv_injective (left_inv_eq_right_inv h id_mul_antipode)

variable (S₀) in
/-- A unital antimultiplicative map that is a left convolution inverse of the identity on an
algebra-generating set is the antipode. -/
theorem eq_antipode_of_adjoin_eq_top (S₀_one : S₀ 1 = 1)
    (S₀_mul : ∀ x y, S₀ (x * y) = S₀ y * S₀ x) (adjoin_eq_top : adjoin R s = ⊤)
    (S₀_convMul_id : ∀ p ∈ s,
      (toConv S₀ * toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p) :
    S₀ = antipode R :=
  eq_antipode_of_convMul_id_eq_one
    (convMul_eq_one_of_adjoin_eq_top_left S₀_one S₀_mul rfl (fun _ _ => rfl)
      adjoin_eq_top S₀_convMul_id)

end Uniqueness

end HopfAlgebra
