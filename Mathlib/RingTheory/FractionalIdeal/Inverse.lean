/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Inverse operator for fractional ideals

This file defines the notation `I⁻¹` where `I` is a not necessarily invertible fractional ideal.
Note that this is somewhat misleading notation in case `I` is not invertible.
The theorem that all nonzero fractional ideals are invertible in a Dedekind domain can be found in
`Mathlib/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `FractionalIdeal.instInv` defines `I⁻¹ := 1 / I`.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

fractional ideal, invertible ideal
-/

assert_not_exists IsDedekindDomain

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

namespace FractionalIdeal

variable {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]
variable {I J : FractionalIdeal R₁⁰ K}

noncomputable instance : Inv (FractionalIdeal R₁⁰ K) := ⟨fun I => 1 / I⟩

theorem inv_eq : I⁻¹ = 1 / I := rfl

theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 := div_zero

theorem inv_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, fractional_div_of_nonzero h⟩ := div_nonzero h

theorem coe_inv_of_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / (J : Submodule R₁ K) := by
  simp_rw [inv_nonzero _ h, coe_one, coe_mk, IsLocalization.coeSubmodule_top]

variable {K}

theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : FractionalIdeal R₁⁰ K) :=
  mem_div_iff_of_nonzero hI

theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ := by
  intro x
  simp only [mem_inv_iff hJ, mem_inv_iff hI]
  exact fun h y hy => h y (hIJ hy)

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * I⁻¹ :=
  le_self_mul_one_div hI

variable (K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) :
    (I : FractionalIdeal R₁⁰ K) ≤ I * (I : FractionalIdeal R₁⁰ K)⁻¹ :=
  le_self_mul_inv coeIdeal_le_one

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ := by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1 from
    congr_arg Units.inv <| @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_nonzero hI).mp hy x hx
  rw [← h]
  apply mul_left_mono I
  apply (le_div_iff_of_nonzero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact mul_mem_mul hy hx

theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩

theorem mul_inv_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
protected theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    I⁻¹.map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ := by
  rw [inv_eq, FractionalIdeal.map_div, FractionalIdeal.map_one, inv_eq]

open Submodule Submodule.IsPrincipal

@[simp]
theorem spanSingleton_inv (x : K) : (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹ :=
  one_div_spanSingleton x

theorem spanSingleton_div_spanSingleton (x y : K) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R₁⁰ (x / y) := by
  rw [div_spanSingleton, mul_comm, spanSingleton_mul_spanSingleton, div_eq_mul_inv]

theorem spanSingleton_div_self {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ x = 1 := by
  rw [spanSingleton_div_spanSingleton, div_self hx, spanSingleton_one]

theorem coe_ideal_span_singleton_div_self {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) / Ideal.span ({x} : Set R₁) = 1 := by
  rw [coeIdeal_span_singleton,
    spanSingleton_div_self K <|
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

theorem spanSingleton_mul_inv {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1 := by
  rw [spanSingleton_inv, spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx, spanSingleton_one]

theorem coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) *
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ = 1 := by
  rw [coeIdeal_span_singleton,
    spanSingleton_mul_inv K <|
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

theorem spanSingleton_inv_mul {x : K} (hx : x ≠ 0) :
    (spanSingleton R₁⁰ x)⁻¹ * spanSingleton R₁⁰ x = 1 := by
  rw [mul_comm, spanSingleton_mul_inv K hx]

theorem coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ * Ideal.span ({x} : Set R₁) = 1 := by
  rw [mul_comm, coe_ideal_span_singleton_mul_inv K hx]

theorem mul_generator_self_inv {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 := by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton, mul_inv_cancel₀, spanSingleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I, generator_I_eq_zero, spanSingleton_zero]

theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) : I * I⁻¹ = 1 :=
  mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩

theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) ≠ 0 := by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_spanSingleton_of_principal I, hg, spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I : Submodule R₁ K))
    rw [hI, mem_zero_iff] at this
    contradiction

theorem isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
    (h : I ≠ 0) : Submodule.IsPrincipal I⁻¹.1 := by
  rw [val_eq_coe, isPrincipal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
    mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm

variable {K}

lemma den_mem_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≠ ⊥) :
    (algebraMap R₁ K) (I.den : R₁) ∈ I⁻¹ := by
  rw [mem_inv_iff hI]
  intro i hi
  rw [← Algebra.smul_def (I.den : R₁) i, ← mem_coe, coe_one]
  suffices Submodule.map (Algebra.linearMap R₁ K) I.num ≤ 1 from
    this <| (den_mul_self_eq_num I).symm ▸ smul_mem_pointwise_smul i I.den I.coeToSubmodule hi
  apply le_trans <| map_mono (show I.num ≤ 1 by simp only [Ideal.one_eq_top, le_top])
  rw [Ideal.one_eq_top, Submodule.map_top, one_eq_range]

lemma num_le_mul_inv (I : FractionalIdeal R₁⁰ K) : I.num ≤ I * I⁻¹ := by
  by_cases hI : I = 0
  · rw [hI, num_zero_eq <| FaithfulSMul.algebraMap_injective R₁ K, zero_mul, zero_eq_bot,
      coeIdeal_bot]
  · rw [mul_comm, ← den_mul_self_eq_num']
    exact mul_right_mono I <| spanSingleton_le_iff_mem.2 (den_mem_inv hI)

lemma bot_lt_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≠ ⊥) : ⊥ < I * I⁻¹ :=
  lt_of_lt_of_le (coeIdeal_ne_zero.2 (hI ∘ num_eq_zero_iff.1)).bot_lt I.num_le_mul_inv

noncomputable instance : InvOneClass (FractionalIdeal R₁⁰ K) := { inv_one := div_one }

end FractionalIdeal
