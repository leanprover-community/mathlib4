/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Algebra.QuadraticAlgebra.Integral
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Quadratic algebras over `ℤ`

For `a b : ℤ`, `QuadraticAlgebra ℤ a b` is an order in `QuadraticAlgebra ℚ a b`.

## Main results

* `QuadraticAlgebra ℚ a b` is the localization of `QuadraticAlgebra ℤ a b` at the nonzero
  integers and its fraction ring.
* `QuadraticAlgebra.Int.isDomain_iff`: `QuadraticAlgebra ℤ a b` is an integral domain iff
  `discr a b` is not a square.
* `QuadraticAlgebra.Int.saturated_iff`: an integral element `z` with `p • z` in the order, for a
  prime `p`, lies in the order iff `discr a b` is not `p ^ 2` times an integer `≡ 0, 1 mod 4`.
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

/-- If `d ∣ s` and `4 * d ^ 2 ∣ s ^ 2 - discr a b`, then `((s - b) / 2 + ω) / d` is integral over
`ℤ`. Its trace is `s / d` and four times its norm is `(s ^ 2 - discr a b) / d ^ 2`. -/
theorem isIntegral_inv_smul_of_dvd {d s : ℤ} (hs : d ∣ s)
    (hs' : 4 * d ^ 2 ∣ s ^ 2 - discr a b) :
    IsIntegral ℤ ((d : ℚ)⁻¹ • (((s - b) / 2 : ℤ) • 1 + ω : QuadraticAlgebra ℚ a b)) := by
  by_cases hd : (d : ℚ) = 0
  · simpa [hd] using isIntegral_zero
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, 2 * t + b = s := by
    refine ⟨(s - b) / 2, ?_⟩
    suffices 2 ∣ (s + b) ∨ 2 ∣ (s - b) by lia
    rw [← Int.prime_two.dvd_mul, ← sq_sub_sq, ← dvd_sub_left (by lia : 2 ∣ 4 * a), sub_sub]
    exact dvd_trans (Dvd.dvd.mul_right (by norm_num) _) (discr_def a b ▸ hs')
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv⟩ := hs'
  refine isIntegral_iff.mpr ⟨⟨u, ?_⟩, ⟨v, ?_⟩⟩ <;> rw [algebraMap_int_eq, eq_intCast]
  · rw [map_smul, add_sub_cancel_right, Int.mul_ediv_cancel_left _ two_ne_zero,
      ← Int.cast_smul_eq_zsmul ℚ, trace_smul_one_add_omega, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hd,
      eq_comm]
    exact_mod_cast hu
  · rw [norm_smul, add_sub_cancel_right, Int.mul_ediv_cancel_left _ two_ne_zero, inv_pow,
      eq_inv_mul_iff_mul_eq₀ (pow_ne_zero 2 hd), ← mul_right_inj' four_ne_zero,
      ← Int.cast_smul_eq_zsmul ℚ, four_mul_norm_smul_one_add_omega, discr_intCast, eq_comm,
      ← mul_assoc]
    exact_mod_cast hv

variable (a b) in
/-- For `1 < |d|`, the `im` part of `(t + ω) / d` is `1 / d`, hence not an integer. -/
theorem im_inv_smul_notMem_range {d : ℤ} (t : ℤ) (hd : 1 < d.natAbs) :
    ((d : ℚ)⁻¹ • (t • 1 + ω : QuadraticAlgebra ℚ a b)).im ∉ Set.range (algebraMap ℤ ℚ) := by
  intro ⟨x, hx⟩
  simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul, mul_one, smul_add, im_add, im_smul,
    im_intCast, smul_eq_mul, mul_zero, im_omega, zero_add,
    ← mul_eq_one_iff_eq_inv₀ (by aesop : (d : ℚ) ≠ 0)] at hx
  rw [← Int.cast_mul, Int.cast_eq_one, Int.mul_eq_one_iff_eq_one_or_neg_one] at hx
  grind

/-- If `discr a b = d ^ 2 * e` with `e ≡ 0, 1 mod 4` and `1 < |d|`, the order is not saturated at
`d`: the element `((d * e - b) / 2 + ω) / d` is integral and lies in the order after scaling by
`d`, but not before. -/
theorem exists_unsaturated_of_sq_mul {d e : ℤ} (hd : 1 < d.natAbs) (he : discr a b = d ^ 2 * e)
    (he' : e % 4 = 0 ∨ e % 4 = 1) :
    ∃ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z ∧
      d • z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) ∧
        z ∉ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) := by
  have hd₀ : (d : ℚ) ≠ 0 := by aesop
  refine ⟨(d : ℚ)⁻¹ • (((d * e - b) / 2 : ℤ) • 1 + ω),
    isIntegral_inv_smul_of_dvd (dvd_mul_right d e) ?_, ?_, ?_⟩
  · rw [he, mul_pow, ← mul_sub, mul_comm, pow_two e, ← mul_sub_one]
    refine mul_dvd_mul_left _ ?_
    obtain _ | _ := he'
    · exact Int.dvd_mul_of_dvd_left <| by lia
    · exact Int.dvd_mul_of_dvd_right <| by lia
  · rw [← Int.cast_smul_eq_zsmul ℚ d, smul_smul, mul_inv_cancel₀ hd₀, one_smul]
    exact ⟨((d * e - b) / 2) • 1 + ω, by ext <;> simp⟩
  · exact fun ⟨x, hx⟩ ↦ im_inv_smul_notMem_range a b ((d * e - b) / 2) hd
      ⟨_, by simpa using congr_arg im hx⟩

/-- If `x` in the order maps to `d • z` with `z` integral and `d ∣ x.im`, then `z` already lies in
the order. -/
theorem mem_range_of_dvd_im {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b} {d : ℤ}
    (hz : IsIntegral ℤ z) (hd : d ≠ 0)
    (hx : algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x = d • z) (him : d ∣ x.im) :
    z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) := by
  obtain ⟨v, hv⟩ := him
  replace hv : v = z.im := by
    have : x.im = d * z.im := by simpa using congr_arg im hx
    rwa [hv, Int.cast_mul, mul_right_inj' (Int.cast_ne_zero.mpr hd)] at this
  obtain ⟨u, hu⟩ : z.re ∈ Set.range (algebraMap ℤ ℚ) :=
    re_mem_range_of_im_mem_range ⟨a, rfl⟩ ⟨b, rfl⟩ hz ⟨v, hv⟩
  refine ⟨u • 1 + v • ω, ?_⟩
  simpa [QuadraticAlgebra.ext_iff] using ⟨hu, hv⟩

/-- If `x` in the order maps to `d • z` with `z` integral, then `discr a b * x.im ^ 2` is `d ^ 2`
times `t ^ 2 - 4 * n`, where `t` and `n` are the trace and the norm of `z`. -/
theorem exists_discr_mul_im_sq_eq {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b}
    {d : ℤ} (hz : IsIntegral ℤ z)
    (hx : algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x = d • z) :
    ∃ t n : ℤ, discr a b * x.im ^ 2 = d ^ 2 * (t ^ 2 - 4 * n) := by
  obtain ⟨⟨t, ht⟩, ⟨n, hn⟩⟩ := isIntegral_iff.mp hz
  simp only [algebraMap_int_eq, eq_intCast] at ht hn
  refine ⟨t, n, ?_⟩
  apply FaithfulSMul.algebraMap_injective ℤ ℚ
  have : x.im = d * z.im := by simpa using congr_arg im hx
  simp [ht, hn, four_mul_norm_eq, this, discr_intCast]
  ring

/-- The order is saturated at the prime `p` iff `discr a b` is not `p ^ 2` times an integer
`≡ 0, 1 mod 4`. -/
theorem saturated_iff (p : ℕ) (hp : p.Prime) :
    (∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        p • z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) →
          z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b))) ↔
      ¬ ∃ e : ℤ, discr a b = (p : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  have hq : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine ⟨fun h ⟨e, he, he'⟩ ↦ ?_, fun h z hz ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨z, hz₁, hz₂, hz₃⟩ := exists_unsaturated_of_sq_mul (d := p) hp.one_lt he he'
    exact hz₃ (h z hz₁ hz₂)
  refine mem_range_of_dvd_im hz hq.ne_zero hx <| hq.dvd_of_dvd_pow (n := 2) ?_
  contrapose h
  obtain ⟨t, n, htn⟩ := exists_discr_mul_im_sq_eq hz hx
  obtain ⟨e, he⟩ := (hq.coprime_iff_not_dvd.mpr h).pow_left.dvd_of_dvd_mul_right
    ⟨t ^ 2 - 4 * n, htn⟩
  refine ⟨e, he, ?_⟩
  obtain rfl | hp₂ := hp.eq_two_or_odd'
  · push_cast at h htn he
    obtain ⟨k, hk⟩ : Odd x.im := by
      rwa [← Int.odd_pow' two_ne_zero, ← Int.not_even_iff_odd, even_iff_two_dvd]
    rw [hk, he] at htn
    grind [Int.sq_emod_four]
  · have := he ▸ discr_emod_four_eq_zero_or_one a b
    rwa [Int.mul_emod, Int.sq_emod_four_eq_one_of_odd hp₂.natCast, one_mul, Int.emod_emod] at this

end Int

end QuadraticAlgebra
