/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.Algebra.QuadraticAlgebra.Integral
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Quadratic algebras over `ℤ`

For `a b : ℤ`, `QuadraticAlgebra ℤ a b` is an order in `QuadraticAlgebra ℚ a b`.

## Main results

* `QuadraticAlgebra ℚ a b` is the localization of `QuadraticAlgebra ℤ a b` at the nonzero
  integers and its fraction ring.
* `QuadraticAlgebra.Int.isDomain_iff`: `QuadraticAlgebra ℤ a b` is an integral domain iff
  `discr a b` is not a square.
* `QuadraticAlgebra.Int.exists_im_den_sq_mul`: if `z` is an integral element of
  `QuadraticAlgebra ℚ a b`, then `discr a b` is the square of the denominator of `z.im` times an
  integer congruent to `0` or `1` modulo `4`.
* `QuadraticAlgebra.Int.exists_isIntegral_notMem_of_sq_mul`: conversely, if
  `discr a b = d ^ 2 * e` with `1 < |d|` and `e` congruent to `0` or `1` modulo `4`, then there is
  an integral element `z` not in `QuadraticAlgebra ℤ a b` such that `d • z` lies in it.
-/

public section

namespace QuadraticAlgebra

open Algebra

namespace Int

variable {a b : ℤ}

noncomputable instance : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  QuadraticAlgebra.algebra ℚ a b

instance : IsScalarTower ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  .of_algHom (baseChange ℚ a b)

@[simp]
theorem re_algebraMap (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).re = x.re := rfl

@[simp]
theorem im_algebraMap (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).im = x.im := rfl

@[simp]
theorem algebraMap_omega : algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) ω = ω :=
  mapRingHom_omega _ a b

@[simp]
theorem norm_algebraMap_eq (x : QuadraticAlgebra ℤ a b) :
    norm (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x) = norm x :=
  norm_mapRingHom (algebraMap ℤ ℚ) a b x

@[simp]
theorem trace_algebraMap_eq (x : QuadraticAlgebra ℤ a b) :
    trace (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x) = trace x :=
  trace_mapRingHom (algebraMap ℤ ℚ) a b x

instance : FaithfulSMul (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr <| baseChange_injective ℚ _ _

open scoped nonZeroDivisors

theorem exists_nat_smul_mem (z : QuadraticAlgebra ℚ a b) :
    ∃ n : ℕ, 0 < n ∧
      n • z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) := by
  obtain ⟨n, hn, x, y, hx, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ x y : ℤ, n * z.re = x ∧ n * z.im = y :=
    ⟨z.re.den * z.im.den, by positivity, z.im.den * z.re.num, z.re.den * z.im.num,
      by push_cast; grind [← Rat.mul_den_eq_num]⟩
  refine ⟨n, hn, x • 1 + y • ω, ?_⟩
  ext <;> simp [hx, hy]

-- TODO: generalize this instance: if `S` is the localization of `R` at `M`, then
-- `QuadraticAlgebra S a b` is the localization of `QuadraticAlgebra R a b` at the image of `M`.
/-- `QuadraticAlgebra ℚ a b` is the localization of the order `QuadraticAlgebra ℤ a b` at the
nonzero integers. -/
noncomputable instance :
    IsLocalization (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰)
      (QuadraticAlgebra ℚ a b) := by
  refine ⟨fun ⟨y, ⟨x, hx, hy⟩⟩ ↦ ?_, fun x ↦ ?_, fun h ↦ ⟨1, by simpa using h⟩⟩
  · dsimp only
    rw [← hy, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ]
    exact IsUnit.map _ <| by simpa [isUnit_iff_ne_zero] using hx
  · obtain ⟨n, hn, ⟨w, hw⟩⟩ := exists_nat_smul_mem x
    exact ⟨⟨w, n, ⟨n, by simpa using hn.ne', rfl⟩⟩, by simp [hw, mul_comm]⟩

instance : IsFractionRing (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) := by
  refine IsLocalization.of_le (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_mem_nonZeroDivisors_iff.mp <| by simpa using hx
  · intro x hx
    rwa [isUnit_iff_norm_isUnit, isUnit_iff_ne_zero, norm_algebraMap_eq, Int.cast_ne_zero,
      ← mem_nonZeroDivisors_iff_ne_zero, norm_mem_nonZeroDivisors_iff]

theorem isDomain_iff :
    IsDomain (QuadraticAlgebra ℤ a b) ↔ ¬ IsSquare (discr a b) := by
  simp [IsFractionRing.isDomain_iff_isField (K := QuadraticAlgebra ℚ a b),
    isField_iff_not_isSquare_discr, discr_intCast]

instance [Fact (¬ IsSquare (discr a b))] : IsDomain (QuadraticAlgebra ℤ a b) :=
  isDomain_iff.mpr Fact.out

/-! ### Maximality of the order -/

/-- The image of `QuadraticAlgebra ℤ a b` in `QuadraticAlgebra ℚ a b`. -/
local notation "𝒪" => Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b))

/-- If `d ∣ 2 * t + b` and `4 * d ^ 2 ∣ (2 * t + b) ^ 2 - discr a b`, then `(t + ω) / d` is integral
over `ℤ`. -/
theorem isIntegral_inv_smul_of_dvd {d t : ℤ} (ht₁ : d ∣ 2 * t + b)
    (ht₂ : 4 * d ^ 2 ∣ (2 * t + b) ^ 2 - discr a b) :
    IsIntegral ℤ ((d : ℚ)⁻¹ • (t • 1 + ω : QuadraticAlgebra ℚ a b)) := by
  by_cases hd : (d : ℚ) = 0
  · simpa [hd] using isIntegral_zero
  obtain ⟨u, hu⟩ := ht₁
  obtain ⟨v, hv⟩ := ht₂
  refine isIntegral_iff.mpr ⟨⟨u, ?_⟩, ⟨v, ?_⟩⟩
  · rw [map_smul, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hd, eq_comm, map_add, trace_omega,
      zsmul_eq_mul, mul_one, trace_intCast, algebraMap_int_eq, eq_intCast]
    exact mod_cast hu
  · rw [norm_smul, smul_eq_mul, inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero 2 hd),
      ← mul_right_inj' four_ne_zero, ← Int.cast_smul_eq_zsmul ℚ, four_mul_norm_smul_one_add_omega,
      discr_intCast, eq_comm, ← mul_assoc, algebraMap_int_eq, eq_intCast]
    exact mod_cast hv

/-- An integral element `z` of `QuadraticAlgebra ℚ a b` lies in `QuadraticAlgebra ℤ a b` iff its
imaginary part is an integer. -/
theorem mem_range_iff_im_mem_range {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    z ∈ 𝒪 ↔ z.im ∈ Set.range (algebraMap ℤ ℚ) := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x.im, by simp [← hx]⟩, fun ⟨v, hv⟩ ↦ ?_⟩
  obtain ⟨u, hu⟩ := re_mem_range_of_im_mem_range ⟨a, rfl⟩ ⟨b, rfl⟩ hz ⟨v, hv⟩
  exact ⟨⟨u, v⟩, by ext <;> simp_all⟩

/-- If `z` is an integral element of `QuadraticAlgebra ℚ a b`, then the denominator of `z.im` times
`z` lies in `QuadraticAlgebra ℤ a b`. -/
theorem im_den_smul_mem {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    (z.im.den : ℤ) • z ∈ 𝒪 :=
  (mem_range_iff_im_mem_range (hz.zsmul _)).mpr (by simp)

private theorem exists_isIntegral_notMem_of_sq_mul_aux {d e : ℤ} (he : discr a b = d ^ 2 * e)
    (he' : 4 ∣ e ^ 2 - e) :
    ∃ t : ℤ, d ∣ 2 * t + b ∧ 4 * d ^ 2 ∣ (2 * t + b) ^ 2 - discr a b := by
  have h : (d * e - b) % 2 = (d ^ 2 * e - discr a b) % 2 := by
    simp [discr_def, Int.sub_emod, Int.mul_emod, Int.add_emod]
  rw [he, Int.sub_self, Int.zero_emod, ← Int.dvd_iff_emod_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  rw [Int.sub_eq_iff_eq_add, eq_comm] at ht
  refine ⟨t, ⟨e, ht⟩, ?_⟩
  obtain ⟨f, hf⟩ := he'
  exact ⟨f, by rw [he, ht, mul_pow, ← mul_sub, hf, mul_left_comm, mul_assoc]⟩

/-- If `discr a b = d ^ 2 * e` with `e` congruent to `0` or `1` modulo `4` and `1 < |d|`, then
there is an integral element `z` of `QuadraticAlgebra ℚ a b` such that `d • z` lies in
`QuadraticAlgebra ℤ a b` but `z` does not. -/
theorem exists_isIntegral_notMem_of_sq_mul {d e : ℤ} (hd : 1 < d.natAbs)
    (he : discr a b = d ^ 2 * e) (he' : e % 4 = 0 ∨ e % 4 = 1) :
    ∃ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z ∧ d • z ∈ 𝒪 ∧ z ∉ 𝒪 := by
  replace he' : 4 ∣ e ^ 2 - e := by
    rw [← Int.modEq_iff_dvd, Int.ModEq, Int.sq_emod_four]
    cases he' <;> lia
  obtain ⟨t, ht₁, ht₂⟩ := exists_isIntegral_notMem_of_sq_mul_aux he he'
  have hz := isIntegral_inv_smul_of_dvd ht₁ ht₂
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by lia)
  refine ⟨(d : ℚ)⁻¹ • (t • 1 + ω : QuadraticAlgebra ℚ a b), hz, ⟨t • 1 + ω, ?_⟩, ?_⟩
  · rw [← Int.cast_smul_eq_zsmul ℚ d, smul_smul, mul_inv_cancel₀ hd', one_smul, map_add,
      map_zsmul, map_one, algebraMap_omega]
  · rintro ⟨y, hy⟩
    have : (y.im : ℚ) * d = 1 := by simpa [← mul_eq_one_iff_eq_inv₀ hd'] using congr_arg im hy
    rw [← Int.cast_mul, Int.cast_eq_one, Int.mul_eq_one_iff_eq_one_or_neg_one] at this
    lia

/-- If `z` is integral and `d • z` is the image of an element `x` of `QuadraticAlgebra ℤ a b`, then
`discr a b * x.im ^ 2` is `d ^ 2` times `t ^ 2 - 4 * n` (here `t` and `n` are the trace and the
norm of `z`). -/
theorem exists_mul_im_sq_eq {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b}
    {d : ℤ} (hz : IsIntegral ℤ z)
    (hx : algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x = d • z) :
    ∃ t n : ℤ, discr a b * x.im ^ 2 = d ^ 2 * (t ^ 2 - 4 * n) := by
  obtain ⟨⟨t, ht⟩, ⟨n, hn⟩⟩ := isIntegral_iff.mp hz
  refine ⟨t, n, ?_⟩
  replace hx : algebraMap ℤ ℚ x.im = d • z.im := by
    simpa using congr_arg im hx
  apply FaithfulSMul.algebraMap_injective ℤ ℚ
  simp_rw [map_mul, map_sub, map_pow, ht, map_mul, hn, map_ofNat, four_mul_norm_eq, sub_sub_cancel,
    discr_intCast, hx, algebraMap_int_eq, eq_intCast, zsmul_eq_mul]
  ring

/-- Let `z` be an integral element such that `d • z` is the image of an element `x` of
`QuadraticAlgebra ℤ a b`, with `d` coprime to `x.im`. Then `discr a b` is `d ^ 2` times an
integer congruent to `0` or `1` modulo `4`. -/
theorem exists_sq_mul_of_isCoprime {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b}
    {d : ℤ} (hz : IsIntegral ℤ z) (hd : IsCoprime d x.im)
    (hx : algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x = d • z) :
    ∃ e : ℤ, discr a b = d ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  obtain ⟨t, n, h⟩ := exists_mul_im_sq_eq hz hx
  obtain ⟨e, he⟩ : d ^ 2 ∣ discr a b := hd.pow.dvd_of_dvd_mul_right ⟨_, h⟩
  refine ⟨e, he, ?_⟩
  obtain hd' | hd' := d.even_or_odd
  · have him : Odd x.im :=
      Int.isCoprime_two_left.mp <| IsCoprime.of_isCoprime_of_dvd_left hd hd'.two_dvd
    have hd₀ : d ≠ 0 := by
      rintro rfl
      simp_all
    rw [he, mul_assoc, mul_right_inj' (Int.pow_ne_zero hd₀)] at h
    replace h := congr_arg (· % 4) h
    rw [Int.mul_emod, Int.sq_emod_four, Int.odd_iff.mp him, mul_one, Int.sub_mul_emod_self_left,
      Int.emod_emod, Int.sq_emod_four] at h
    lia
  · replace he := congr_arg (· % 4) he
    rw [Int.mul_emod, Int.sq_emod_four, Int.odd_iff.mp hd', one_mul, Int.emod_emod] at he
    exact he ▸ discr_emod_four_eq_zero_or_one a b

/-- If `z` is an integral element of `QuadraticAlgebra ℚ a b`, then `discr a b` is the square of
the denominator of `z.im` times an integer congruent to `0` or `1` modulo `4`. -/
theorem exists_im_den_sq_mul {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    ∃ e : ℤ, discr a b = (z.im.den : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  obtain ⟨x, hx⟩ := im_den_smul_mem hz
  refine exists_sq_mul_of_isCoprime hz ?_ hx
  rw [show x.im = z.im.num by simpa using congr_arg im hx]
  exact (Rat.isCoprime_num_den z.im).symm

end Int

end QuadraticAlgebra
