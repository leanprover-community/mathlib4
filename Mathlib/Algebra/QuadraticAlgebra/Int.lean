/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Quadratic algebras over `ℤ`

For `a b : ℤ`, the quadratic algebra `QuadraticAlgebra ℤ a b` is an order in
`QuadraticAlgebra ℚ a b`: a free `ℤ`-module of rank `2` whose fraction ring is
`QuadraticAlgebra ℚ a b`. This file establishes that relation, and then determines for which
parameters the order is maximal, that is, is the integral closure of `ℤ` in
`QuadraticAlgebra ℚ a b`. This happens exactly when `discr a b` is a fundamental discriminant.

## Main definitions

* `QuadraticAlgebra.Int.algEquivIntegralClosure`: when `discr a b` is a fundamental discriminant,
  the isomorphism between `QuadraticAlgebra ℤ a b` and the integral closure of `ℤ` in
  `QuadraticAlgebra ℚ a b`.

## Main results

* `QuadraticAlgebra ℚ a b` is the localization of `QuadraticAlgebra ℤ a b` at the nonzero
  integers, and its fraction ring.
* `QuadraticAlgebra.Int.isDomain_iff`: `QuadraticAlgebra ℤ a b` is an integral domain iff
  `discr a b` is not a square.
* `QuadraticAlgebra.Int.isIntegral_iff`: an element of `QuadraticAlgebra ℚ a b` is integral over
  `ℤ` iff its trace and its norm are integers.
* `QuadraticAlgebra.Int.isIntegralClosure_iff`: `QuadraticAlgebra ℤ a b` is the integral closure
  of `ℤ` in `QuadraticAlgebra ℚ a b` iff `discr a b` is a fundamental discriminant.
* `QuadraticAlgebra.Int.isIntegrallyClosed_iff`: `QuadraticAlgebra ℤ a b` is integrally closed iff
  `discr a b` is a fundamental discriminant.

## Tags

quadratic algebra, quadratic order, integral closure, fundamental discriminant
-/

@[expose] public section

namespace QuadraticAlgebra

open Algebra

namespace Int

variable {a b : ℤ}

noncomputable instance : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  (baseChange ℚ a b).toRingHom.toAlgebra

instance : IsScalarTower ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  .of_algHom (baseChange ℚ a b)

/-- The algebra map of the order into `QuadraticAlgebra ℚ a b` is the base change map. -/
theorem algebraMap_eq (x : QuadraticAlgebra ℤ a b) :
    algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x = baseChange ℚ a b x := rfl

/-- The algebra map preserves the `re` part. -/
@[simp]
theorem algebraMap_re_eq (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).re = x.re := by
  simp [algebraMap_eq, re_baseChange_apply ℚ]

/-- The algebra map preserves the `im` part. -/
@[simp]
theorem algebraMap_im_eq (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).im = x.im := by
  simp [algebraMap_eq, im_baseChange_apply ℚ]

instance : FaithfulSMul (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr <| baseChange_injective ℚ _ _

/-- The discriminant commutes with the coercion `ℤ → ℚ`. -/
theorem discr_intCast :
    discr (a : ℚ) (b : ℚ) = discr a b := by
  simpa using discr_algebraMap (S := ℚ) a b

open scoped nonZeroDivisors

/-- Every element of `QuadraticAlgebra ℚ a b` has a positive integer denominator. -/
theorem exists_nat_smul_mem (z : QuadraticAlgebra ℚ a b) :
    ∃ n : ℕ, 0 < n ∧ n • z ∈ Set.range (baseChange ℚ a b) := by
  obtain ⟨n, hn, x, y, hx, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ x y : ℤ, n * z.re = x ∧ n * z.im = y :=
    ⟨z.re.den * z.im.den, by positivity, z.im.den * z.re.num, z.re.den * z.im.num,
      by push_cast; grind [← Rat.mul_den_eq_num]⟩
  refine ⟨n, hn, x • 1 + y • ω, ?_⟩
  ext <;> simp [re_baseChange_apply ℚ, im_baseChange_apply ℚ, hx, hy]

/-- `QuadraticAlgebra ℚ a b` is the localization of the order `QuadraticAlgebra ℤ a b` at the
nonzero integers. This is not `IsFractionRing` in general: `QuadraticAlgebra ℤ a b` need not be a
domain (see `isDomain_iff`). -/
noncomputable instance :
    IsLocalization (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰)
      (QuadraticAlgebra ℚ a b) := by
  refine ⟨fun ⟨y, ⟨x, hx, hy⟩⟩ ↦ ?_, fun x ↦ ?_, fun h ↦ ⟨1, by simpa using h⟩⟩
  · dsimp only
    rw [← hy, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ]
    exact IsUnit.map _ <| by simpa [isUnit_iff_ne_zero] using hx
  · obtain ⟨n, hn, ⟨w, hw⟩⟩ := exists_nat_smul_mem x
    exact ⟨⟨w, n, ⟨n, by simpa using hn.ne', rfl⟩⟩, by simp [algebraMap_eq, hw, mul_comm]⟩

instance : IsFractionRing (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) := by
  refine IsLocalization.of_le (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_mem_nonZeroDivisors_iff.mp <| by simpa using hx
  · intro x hx
    rwa [isUnit_iff_norm_isUnit, isUnit_iff_ne_zero, algebraMap_eq, norm_baseChange ℚ a b,
      eq_intCast, Int.cast_ne_zero, ← mem_nonZeroDivisors_iff_ne_zero, norm_mem_nonZeroDivisors_iff]

/-- The order `QuadraticAlgebra ℤ a b` is a domain iff `discr a b` is not a square. -/
theorem isDomain_iff :
    IsDomain (QuadraticAlgebra ℤ a b) ↔ ¬ IsSquare (discr a b) := by
  simp [IsFractionRing.isDomain_iff_isField (K := QuadraticAlgebra ℚ a b),
    isField_iff_not_isSquare_discr, discr_intCast]

/-!
### Maximality of the order

In this section, we determine for which `a b : ℤ` the order `QuadraticAlgebra ℤ a b` is the
integral closure of `ℤ` in `QuadraticAlgebra ℚ a b`, the answer being that `discr a b` must be a
fundamental discriminant (see `isIntegralClosure_iff`).

Everything rests on the pivot `isIntegral_iff`: an element of `QuadraticAlgebra ℚ a b` is integral
over `ℤ` iff its trace and its norm are integers.

Being the integral closure is a local condition: it suffices that the order be saturated at every
prime `p`, meaning that `p • z` lying in the order forces `z` to lie in it, for `z` integral (see
`isIntegralClosure_iff_forall_prime`). This is proved by descent on the smallest `n` such that
`n • z` lies in the order, removing one prime factor of `n` at a time.

Saturation at `p` is then made explicit: it fails exactly when `discr a b = p ^ 2 * e` for some
`e ≡ 0, 1 mod 4` (see `saturated_iff_of_odd` and `saturated_two_iff`). In one direction, the
element witnessing the failure is `((s - b) / 2 + ω) / p` with `s = p * e`, whose trace and norm
are integers while its `im` part is not (see `exists_unsaturated_of_sq_mul`). In the other, the
identity `discr a b * x.im ^ 2 = d ^ 2 * (t ^ 2 - 4 * n)` of `exists_discr_mul_im_sq_eq` forces
`p ^ 2 ∣ discr a b` as soon as `p` does not divide `x.im`, and the condition on `e` mod `4` is
then automatic for `p` odd and requires `x.im` to be odd for `p = 2`.
-/

/-- The conjugate of an integral element is integral. -/
theorem isIntegral_star {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    IsIntegral ℤ (star z) :=
  hz.map (starRingEnd _).toIntAlgHom

/-- The trace of an integral element is an integer. -/
theorem trace_mem_range_of_isIntegral {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    trace z ∈ Set.range (algebraMap ℤ ℚ) :=
  IsIntegrallyClosed.isIntegral_iff.mp <|
    (algebraMap_trace_eq_add_star z ▸ hz.add (isIntegral_star hz)).tower_bot
      (FaithfulSMul.algebraMap_injective _ _)

/-- The norm of an integral element is an integer. -/
theorem norm_mem_range_of_isIntegral {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    norm z ∈ Set.range (algebraMap ℤ ℚ) :=
  IsIntegrallyClosed.isIntegral_iff.mp <|
    (algebraMap_norm_eq_mul_star z ▸ hz.mul (isIntegral_star hz)).tower_bot
      (FaithfulSMul.algebraMap_injective _ _)

open Polynomial in
/-- An element of `QuadraticAlgebra ℚ a b` is integral over `ℤ` iff its trace and its norm are
integers. -/
theorem isIntegral_iff {z : QuadraticAlgebra ℚ a b} :
    IsIntegral ℤ z ↔
      trace z ∈ Set.range (algebraMap ℤ ℚ) ∧ norm z ∈ Set.range (algebraMap ℤ ℚ) := by
  refine ⟨fun h ↦ ⟨trace_mem_range_of_isIntegral h, norm_mem_range_of_isIntegral h⟩,
    fun ⟨⟨t, ht⟩, ⟨n, hn⟩⟩ ↦ ⟨X ^ 2 - C t * X + C n, by monicity!, ?_⟩⟩
  simp only [algebraMap_int_eq, eq_intCast] at ht hn
  simpa only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_X, eval₂_C,
    IsScalarTower.algebraMap_apply ℤ ℚ (QuadraticAlgebra ℚ a b), eq_intCast (algebraMap ℤ ℚ),
    ht, hn, ← Algebra.smul_def] using sq_sub_trace_smul_add_norm_eq_zero z

/-- The generator `ω` is integral over `ℤ`. -/
theorem isIntegral_omega :
    IsIntegral ℤ (ω : QuadraticAlgebra ℚ a b) :=
  isIntegral_iff.mpr ⟨by simp, -a, by simp [norm_def]⟩

/-- The trace of `t • 1 + ω` is `2 * t + b`. -/
theorem trace_smul_one_add_omega (t : ℤ) :
    trace (t • 1 + ω : QuadraticAlgebra ℚ a b) = 2 * t + b := by
  simp

/-- Four times the norm of `t • 1 + ω` is `(2 * t + b) ^ 2 - discr a b`. -/
theorem four_mul_norm_smul_one_add_omega (t : ℤ) :
    4 * norm (t • 1 + ω : QuadraticAlgebra ℚ a b) = (2 * t + b) ^ 2 - discr a b := by
  rw [four_mul_norm_eq, trace_smul_one_add_omega]
  simp [discr_intCast]

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
    exact dvd_trans (by lia) hs'
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv⟩ := hs'
  refine isIntegral_iff.mpr ⟨⟨u, ?_⟩, ⟨v, ?_⟩⟩ <;> rw [algebraMap_int_eq, eq_intCast]
  · rw [map_smul, add_sub_cancel_right, Int.mul_ediv_cancel_left _ two_ne_zero,
      trace_smul_one_add_omega, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hd, eq_comm]
    exact_mod_cast hu
  · rw [norm_smul, add_sub_cancel_right, Int.mul_ediv_cancel_left _ two_ne_zero, inv_pow,
      eq_inv_mul_iff_mul_eq₀ (by aesop), ← mul_right_inj' four_ne_zero,
      four_mul_norm_smul_one_add_omega, eq_comm, ← mul_assoc]
    exact_mod_cast hv

variable (a b) in
/-- For `1 < |d|`, the `im` part of `(t + ω) / d` is `1 / d`, hence not an integer. -/
theorem im_inv_smul_notMem_range {d : ℤ} (t : ℤ) (hd : (d : ℚ) ≠ 0) (hd' : 1 < d.natAbs) :
    ((d : ℚ)⁻¹ • (t • 1 + ω : QuadraticAlgebra ℚ a b)).im ∉ Set.range (algebraMap ℤ ℚ) := by
  intro ⟨x, hx⟩
  simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul, mul_one, smul_add, im_add, im_smul,
    im_intCast, smul_eq_mul, mul_zero, im_omega, zero_add, ← mul_eq_one_iff_eq_inv₀ hd] at hx
  rw [← Int.cast_mul, Int.cast_eq_one, Int.mul_eq_one_iff_eq_one_or_neg_one] at hx
  grind

/-- If `discr a b = d ^ 2 * e` with `e ≡ 0, 1 mod 4` and `1 < |d|`, the order is not saturated at
`d`: the element `((d * e - b) / 2 + ω) / d` is integral and lies in the order after scaling by
`d`, but not before. -/
theorem exists_unsaturated_of_sq_mul {d e : ℤ} (hd : 1 < d.natAbs) (he : discr a b = d ^ 2 * e)
    (he' : e % 4 = 0 ∨ e % 4 = 1) :
    ∃ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z ∧
      d • z ∈ Set.range (baseChange ℚ a b) ∧ z ∉ Set.range (baseChange ℚ a b) := by
  have hd₀ : (d : ℚ) ≠ 0 := by aesop
  refine ⟨(d : ℚ)⁻¹ • (((d * e - b) / 2 : ℤ) • 1 + ω),
    isIntegral_inv_smul_of_dvd (dvd_mul_right d e) ?_, ?_, ?_⟩
  · rw [he, mul_pow, ← mul_sub, mul_comm, pow_two e, ← mul_sub_one]
    refine mul_dvd_mul_left _ ?_
    obtain _ | _ := he'
    · exact Int.dvd_mul_of_dvd_left <| by lia
    · exact Int.dvd_mul_of_dvd_right <| by lia
  · rw [← Int.cast_smul_eq_zsmul ℚ d, smul_smul, mul_inv_cancel₀ hd₀, one_smul]
    exact ⟨((d * e - b) / 2) • 1 + ω, by simp [baseChange_omega ℚ]⟩
  · exact fun ⟨x, hx⟩ ↦ im_inv_smul_notMem_range a b ((d * e - b) / 2) hd₀ hd
      ⟨_, by simpa [im_baseChange_apply ℚ] using congr_arg im hx⟩

/-- For an integral element, an integer `im` part forces an integer `re` part. -/
theorem re_mem_range_of_im_mem_range {z : QuadraticAlgebra ℚ a b} (h : IsIntegral ℤ z)
    (him : z.im ∈ Set.range (algebraMap ℤ ℚ)) : z.re ∈ Set.range (algebraMap ℤ ℚ) := by
  obtain ⟨m, hm⟩ := him
  have : IsIntegral ℤ (z - m • ω) :=  h.sub (isIntegral_omega.smul _)
  rwa [← re_smul_add_im_smul z, ← IsScalarTower.algebraMap_smul ℚ m, hm, add_sub_cancel_right,
    ← algebraMap_eq_smul_one, ← IsScalarTower.coe_toAlgHom' ℤ, isIntegral_algHom_iff _
    (FaithfulSMul.algebraMap_injective _ _), IsIntegrallyClosed.isIntegral_iff] at this

/-- If `x` in the order maps to `d • z` with `z` integral and `d ∣ x.im`, then `z` already lies in
the order. -/
theorem mem_range_of_dvd_im {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b} {d : ℤ}
    (hz : IsIntegral ℤ z) (hd : d ≠ 0) (hx : baseChange ℚ a b x = d • z) (him : d ∣ x.im) :
    z ∈ Set.range (baseChange ℚ a b) := by
  obtain ⟨v, hv⟩ := him
  replace hv : v = z.im := by
    have : x.im = d * z.im := by simpa [im_baseChange_apply ℚ] using congr_arg im hx
    rwa [hv, Int.cast_mul, mul_right_inj' (Int.cast_ne_zero.mpr hd)] at this
  obtain ⟨u, hu⟩ : z.re ∈ Set.range (algebraMap ℤ ℚ) := re_mem_range_of_im_mem_range hz ⟨v, hv⟩
  refine ⟨u • 1 + v • ω, ?_⟩
  simpa [QuadraticAlgebra.ext_iff, im_baseChange_apply ℚ, re_baseChange_apply ℚ] using ⟨hu, hv⟩

/-- If `x` in the order maps to `d • z` with `z` integral, then `discr a b * x.im ^ 2` is `d ^ 2`
times `t ^ 2 - 4 * n`, where `t` and `n` are the trace and the norm of `z`. -/
theorem exists_discr_mul_im_sq_eq {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b}
    {d : ℤ} (hz : IsIntegral ℤ z) (hx : baseChange ℚ a b x = d • z) :
    ∃ t n : ℤ, discr a b * x.im ^ 2 = d ^ 2 * (t ^ 2 - 4 * n) := by
  obtain ⟨⟨t, ht⟩, ⟨n, hn⟩⟩ := isIntegral_iff.mp hz
  simp only [algebraMap_int_eq, eq_intCast] at ht hn
  refine ⟨t, n, ?_⟩
  apply FaithfulSMul.algebraMap_injective ℤ ℚ
  have : x.im = d * z.im := by simpa [im_baseChange_apply ℚ] using congr_arg im hx
  simp [ht, hn, four_mul_norm_eq, this, discr_intCast]
  ring

/-- For `p` an odd prime, the order is saturated at `p` iff `discr a b` is not `p ^ 2` times an
integer `≡ 0, 1 mod 4`. For `p` odd that last condition is automatic, so this amounts to
`p ^ 2 ∤ discr a b`. -/
theorem saturated_iff_of_odd (p : ℕ) (hp₁ : p.Prime) (hp₂ : Odd p) :
    (∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        p • z ∈ Set.range (baseChange ℚ a b) → z ∈ Set.range (baseChange ℚ a b)) ↔
      ¬ ∃ e : ℤ, discr a b = (p : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  let q := (p : ℤ)
  have hq₁ : Prime q := Nat.prime_iff_prime_int.mp hp₁
  have hq₂ : Odd q := Odd.natCast hp₂
  refine ⟨fun h ⟨e, he, he'⟩ ↦ ?_,
  fun h z hz ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨z, hz₁, hz₂, hz₃⟩ := exists_unsaturated_of_sq_mul (by exact hp₁.one_lt) he he'
    exact hz₃ (h z hz₁ hz₂)
  · refine mem_range_of_dvd_im hz hq₁.ne_zero hx <| Prime.dvd_of_dvd_pow hq₁ (n := 2) ?_
    contrapose! h
    obtain ⟨t, n, htn⟩ := exists_discr_mul_im_sq_eq hz hx
    obtain ⟨e, he⟩ := ((Prime.coprime_iff_not_dvd hq₁).mpr h).pow_left.dvd_of_dvd_mul_right
      ⟨t ^ 2 - 4 * n, htn⟩
    refine ⟨e, he, ?_⟩
    have := he ▸ discr_emod_four a b
    rwa [Int.mul_emod, Int.sq_emod_four, Int.odd_iff.mp hq₂, one_mul, Int.emod_emod] at this

/-- The order is saturated at `2` iff `discr a b` is not `4` times an integer `≡ 0, 1 mod 4`,
that is, iff `discr a b` is not four times another discriminant. -/
theorem saturated_two_iff :
    (∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        2 • z ∈ Set.range (baseChange ℚ a b) → z ∈ Set.range (baseChange ℚ a b)) ↔
      ¬ ∃ e : ℤ, discr a b = (2 : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  refine ⟨fun hsat ⟨e, he, he'⟩ ↦ ?_, fun h z hz ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨z, hz₁, hz₂, hz₃⟩ := exists_unsaturated_of_sq_mul (d := 2) (by norm_num) he he'
    exact hz₃ (hsat z hz₁ hz₂)
  · refine mem_range_of_dvd_im hz two_ne_zero hx <| Int.prime_two.dvd_of_dvd_pow (n := 2) ?_
    contrapose! h
    obtain ⟨t, n, htn⟩ := exists_discr_mul_im_sq_eq hz hx
    obtain ⟨e, he⟩ := ((Prime.coprime_iff_not_dvd Int.prime_two).mpr h).pow_left
      |>.dvd_of_dvd_mul_right ⟨t ^ 2 - 4 * n, htn⟩
    refine ⟨e, he, ?_⟩
    have h₁ : Odd x.im := by rwa [← Int.odd_pow' two_ne_zero, ← Int.not_two_dvd_iff_odd]
    have h₂ : x.im ^ 2 * e = t ^ 2 - 4 * n :=
      mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by grind)
    have := Int.emod_two_eq t
    rwa [← Int.sq_emod_four, ← Int.sub_mul_emod_self_left, ← h₂, Int.mul_emod, Int.sq_emod_four,
      Int.odd_iff.mp h₁, one_mul, Int.emod_emod] at this

/-- The order is the integral closure of `ℤ` in `QuadraticAlgebra ℚ a b` iff it is saturated at
every prime. -/
theorem isIntegralClosure_iff_forall_prime :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) ↔
      ∀ p : ℕ, p.Prime → ∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        p • z ∈ Set.range (baseChange ℚ a b) → z ∈ Set.range (baseChange ℚ a b) := by
  rw [isIntegralClosure_iff]
  refine ⟨fun h p _ z hz _ ↦ (h z).mp hz, fun h z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · obtain ⟨n, hn, hw⟩ := exists_nat_smul_mem z
    induction n using Nat.strong_induction_on generalizing z with
    | h n h_ind =>
        obtain rfl | h' := eq_or_ne n 1
        · rwa [one_smul] at hw
        · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h'
          refine h p hp z hz <| h_ind (n / p) (Nat.div_lt_self hn hp.one_lt) _ (hz.nsmul p) ?_ ?_
          · exact (Nat.lt_div_iff_mul_lt' hpn 0).mpr hn
          · rwa [smul_smul, Nat.div_mul_cancel hpn]
  · rintro ⟨w, rfl⟩
    exact (Algebra.IsIntegral.isIntegral w).map (baseChange ℚ a b)

/-- The order `QuadraticAlgebra ℤ a b` is the integral closure of `ℤ` in `QuadraticAlgebra ℚ a b`
iff `discr a b` is a fundamental discriminant. -/
theorem isIntegralClosure_iff :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) ↔
      Int.IsFundamentalDiscr (discr a b) := by
  simp_rw (config := {singlePass := true}) +contextual [isIntegralClosure_iff_forall_prime,
    Int.isFundamentalDiscr_iff_forall_prime, Nat.forall_prime_iff_two_and_odd, saturated_two_iff,
    saturated_iff_of_odd, Nat.cast_ofNat]
  exact (and_iff_right (discr_emod_four a b)).symm

/-- The order `QuadraticAlgebra ℤ a b` is integrally closed iff `discr a b` is a fundamental
discriminant. -/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed (QuadraticAlgebra ℤ a b) ↔ Int.IsFundamentalDiscr (discr a b) := by
  rw [← isIntegralClosure_iff, isIntegrallyClosed_iff_isIntegrallyClosedIn
    (K := QuadraticAlgebra ℚ a b)]
  exact ⟨fun _ ↦ IsIntegralClosure.of_isIntegrallyClosedIn,
    fun _ ↦ IsIntegrallyClosedIn.of_isIntegralClosure ℤ⟩

/-- When `discr a b` is a fundamental discriminant, `QuadraticAlgebra ℤ a b` is isomorphic, as a
`ℤ`-algebra, to the integral closure of `ℤ` in `QuadraticAlgebra ℚ a b`. -/
noncomputable def algEquivIntegralClosure (h : Int.IsFundamentalDiscr (discr a b)) :
    QuadraticAlgebra ℤ a b ≃ₐ[ℤ] integralClosure ℤ (QuadraticAlgebra ℚ a b) :=
  letI := isIntegralClosure_iff.mpr h
  IsIntegralClosure.equiv ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)
    (integralClosure ℤ (QuadraticAlgebra ℚ a b))

/-- If `D` is a fundamental discriminant, the quadratic algebra with parameters `D / 4` and
`D % 4` has discriminant `D`. -/
theorem _root_.Int.IsFundamentalDiscr.discr_ediv_four_emod_four {D : ℤ}
    (h : Int.IsFundamentalDiscr D) : discr (D / 4) (D % 4) = D := by
  have : (D % 4) ^ 2 = D % 4 := by grind [h.1]
  rw [discr_def, this]
  lia

end Int

end QuadraticAlgebra
