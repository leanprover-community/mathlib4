/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee, LegaSage
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

/-!
# Wronskian of a pair of polynomial

This file defines Wronskian of a pair of polynomials, which is `W(a, b) = ab' - a'b`.
We also prove basic properties of it.

## Main declarations

- `Polynomial.wronskian_eq_of_sum_zero`: We have `W(a, b) = W(b, c)` when `a + b + c = 0`.
- `Polynomial.degree_wronskian_lt_add`: Degree of Wronskian `W(a, b)` is strictly smaller than
  the sum of degrees of `a` and `b`
- `Polynomial.natDegree_wronskian_lt_add`: `natDegree` version of the above theorem.
  We need to assume that the Wronskian is nonzero. (Otherwise, `a = b = 1` gives a counterexample.)
- `Polynomial.exists_smul_add_eq_zero_of_wronskian_eq_zero`: over a characteristic-zero field,
  two polynomials with vanishing Wronskian satisfy a nontrivial scalar relation.
- `Polynomial.eq_smul_pow_of_weighted_derivative_eq_zero`: solutions of the weighted derivative
  equation `a * f' - n * a' * f = 0` are scalar multiples of `a ^ n` when `a` is nonzero.

## TODO

- Define Wronskian for n-tuple of polynomials, not necessarily two.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Wronskian of a pair of polynomials, `W(a, b) = ab' - a'b`. -/
def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b

variable (R) in
/-- `Polynomial.wronskian` as a bilinear map. -/
def wronskianBilin : R[X] →ₗ[R] R[X] →ₗ[R] R[X] :=
  (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative

@[simp]
theorem wronskianBilin_apply (a b : R[X]) : wronskianBilin R a b = wronskian a b := rfl

@[simp]
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  rw [← wronskianBilin_apply 0 a, map_zero]; rfl

@[simp]
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := (wronskianBilin R a).map_zero

theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b :=
  LinearMap.map_neg₂ (wronskianBilin R) a b

theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b :=
  (wronskianBilin R a).map_neg b

theorem wronskian_add_right (a b c : R[X]) : wronskian a (b + c) = wronskian a b + wronskian a c :=
  (wronskianBilin R a).map_add b c

theorem wronskian_add_left (a b c : R[X]) : wronskian (a + b) c = wronskian a c + wronskian b c :=
  (wronskianBilin R).map_add₂ a b c

theorem wronskian_self_eq_zero (a : R[X]) : wronskian a a = 0 := by
  rw [wronskian, mul_comm, sub_self]

theorem isAlt_wronskianBilin : (wronskianBilin R).IsAlt := wronskian_self_eq_zero

theorem wronskian_neg_eq (a b : R[X]) : -wronskian a b = wronskian b a :=
  LinearMap.IsAlt.neg isAlt_wronskianBilin a b

theorem wronskian_eq_of_sum_zero {a b c : R[X]} (hAdd : a + b + c = 0) :
    wronskian a b = wronskian b c := isAlt_wronskianBilin.eq_of_add_add_eq_zero hAdd

/-- Degree of `W(a,b)` is strictly less than the sum of degrees of `a` and `b` (both nonzero). -/
theorem degree_wronskian_lt_add {a b : R[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left =>
        apply lt_of_le_of_lt
        · exact degree_mul_le a (derivative b)
        · rw [← Polynomial.degree_ne_bot] at ha
          rw [WithBot.add_lt_add_iff_left ha]
          exact Polynomial.degree_derivative_lt hb
      case right =>
        apply lt_of_le_of_lt
        · exact degree_mul_le (derivative a) b
        · rw [← Polynomial.degree_ne_bot] at hb
          rw [WithBot.add_lt_add_iff_right hb]
          exact Polynomial.degree_derivative_lt ha

/--
`natDegree` version of the above theorem.
Note this would be false with just `(ha : a ≠ 0)` and `(hb : b ≠ 0)`,
since when `a = b = 1` we have `(wronskian a b).natDegree = a.natDegree = b.natDegree = 0`.
-/
theorem natDegree_wronskian_lt_add {a b : R[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a ≠ 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b ≠ 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe, WithBot.coe_add]
  convert! ← degree_wronskian_lt_add ha hb
  · exact Polynomial.degree_eq_natDegree hw
  · exact Polynomial.degree_eq_natDegree ha
  · exact Polynomial.degree_eq_natDegree hb

/--
For coprime polynomials `a` and `b`, their Wronskian is zero
if and only if their derivatives are zeros.
-/
theorem _root_.IsCoprime.wronskian_eq_zero_iff
    [NoZeroDivisors R] {a b : R[X]} (hc : IsCoprime a b) :
    wronskian a b = 0 ↔ derivative a = 0 ∧ derivative b = 0 where
  mp hw := by
    rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ _
  mpr hdab := by
    obtain ⟨hda, hdb⟩ := hdab
    rw [wronskian]
    rw [hda, hdb]; simp only [mul_zero, zero_mul, sub_self]

private theorem wronskian_mul_left (g r s : R[X]) :
    wronskian (g * r) (g * s) = g ^ 2 * wronskian r s := by
  simp only [wronskian, derivative_mul]
  ring

/-- If two polynomials over a characteristic-zero field have zero Wronskian, then they satisfy
a nontrivial linear relation over the coefficient field. This includes the cases in which one or
both polynomials vanish. -/
theorem exists_smul_add_eq_zero_of_wronskian_eq_zero
    {K : Type*} [Field K] [CharZero K] (r s : K[X]) (hw : wronskian r s = 0) :
    ∃ c d : K, (c ≠ 0 ∨ d ≠ 0) ∧ c • r + d • s = 0 := by
  classical
  by_cases hs : s = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, by simp [hs]⟩
  letI := EuclideanDomain.gcdMonoid K[X]
  let g : K[X] := gcd r s
  let r' : K[X] := r / g
  let s' : K[X] := s / g
  have hg : g ≠ 0 := gcd_ne_zero_of_right hs
  have hr_factor : g * r' = r :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left r s)
  have hs_factor : g * s' = s :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right r s)
  have hcop : IsCoprime r' s' := isCoprime_div_gcd_div_gcd hs
  have hw' : wronskian r' s' = 0 := by
    have hscaled : g ^ 2 * wronskian r' s' = 0 := by
      rw [← wronskian_mul_left, hr_factor, hs_factor, hw]
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hg)
  have hderiv := hcop.wronskian_eq_zero_iff.mp hw'
  have hr_const : r' = C (r'.coeff 0) := eq_C_of_derivative_eq_zero hderiv.1
  have hs_const : s' = C (s'.coeff 0) := eq_C_of_derivative_eq_zero hderiv.2
  have hs' : s' ≠ 0 := right_div_gcd_ne_zero hs
  have hs_coeff : s'.coeff 0 ≠ 0 := by
    intro h
    apply hs'
    rw [hs_const, h, map_zero]
  refine ⟨s'.coeff 0, -r'.coeff 0, Or.inl hs_coeff, ?_⟩
  rw [← hr_factor, ← hs_factor, hr_const, hs_const]
  simp only [smul_eq_C_mul, coeff_C_zero, map_neg]
  ring

/-- If the right-hand polynomial is nonzero, vanishing Wronskian says that the left-hand
polynomial is a scalar multiple of it. -/
theorem eq_smul_of_wronskian_eq_zero_right
    {K : Type*} [Field K] [CharZero K] (r s : K[X]) (hs : s ≠ 0)
    (hw : wronskian r s = 0) : ∃ c : K, r = c • s := by
  obtain ⟨c, d, hcd, hrel⟩ := exists_smul_add_eq_zero_of_wronskian_eq_zero r s hw
  have hc : c ≠ 0 := by
    intro hc
    have hd : d ≠ 0 := hcd.resolve_left (fun h ↦ h hc)
    exact (smul_ne_zero hd hs) (by simpa [hc] using hrel)
  refine ⟨-(c⁻¹ * d), ?_⟩
  calc
    r = c⁻¹ • (c • r) := by simp [smul_smul, hc]
    _ = c⁻¹ • (-(d • s)) := by rw [eq_neg_of_add_eq_zero_left hrel]
    _ = -(c⁻¹ * d) • s := by simp [smul_smul]

/-- If the left-hand polynomial is nonzero, vanishing Wronskian says that the right-hand
polynomial is a scalar multiple of it. -/
theorem eq_smul_of_wronskian_eq_zero_left
    {K : Type*} [Field K] [CharZero K] (r s : K[X]) (hr : r ≠ 0)
    (hw : wronskian r s = 0) : ∃ c : K, s = c • r := by
  apply eq_smul_of_wronskian_eq_zero_right s r hr
  rw [← wronskian_neg_eq, hw, neg_zero]

/-- If `a * derivative f - n * derivative a * f = 0` and `a` is nonzero, then `f` is a scalar
multiple of `a ^ n`. -/
theorem eq_smul_pow_of_weighted_derivative_eq_zero
    {K : Type*} [Field K] [CharZero K] (a f : K[X]) (n : ℕ) (ha : a ≠ 0)
    (hweighted : a * derivative f - C (n : K) * derivative a * f = 0) :
    ∃ c : K, f = c • a ^ n := by
  have hw : wronskian (a ^ n) f = 0 := by
    cases n with
    | zero =>
        have hdf : derivative f = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_left ha
          simpa using hweighted
        simp [wronskian, hdf]
    | succ n =>
        have hweighted' :
            a * derivative f - C ((n : K) + 1) * derivative a * f = 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using hweighted
        rw [wronskian, derivative_pow_succ, pow_succ]
        calc
          a ^ n * a * derivative f - (C (n + 1 : K) * a ^ n * derivative a) * f =
              a ^ n * (a * derivative f - C (n + 1 : K) * derivative a * f) := by ring
          _ = 0 := by rw [hweighted', mul_zero]
  exact eq_smul_of_wronskian_eq_zero_left (a ^ n) f (pow_ne_zero n ha) hw

end Polynomial
