/-
Copyright (c) 2026 darkhipo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: darkhipo
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Monoid

/-!
# Exactness of the periodic trapezoidal rule on characters

The `n`-point periodic trapezoidal rule (the average of `F` over the `n` equally spaced
points `2 * π * j / n` on the circle of circumference `2 * π`) reproduces the mean of every
character `x ↦ e^{i m x}` *exactly*: its error functional `Eₙ = circleMean - mean` annihilates
every character except the aliased frequencies `m ≠ 0` with `n ∣ m`, where it equals `-1`
(`error_char`).

The mechanism is algebraic, not analytic: the sampled sum `∑_{j < n} e^{2 π i m j / n}` equals
`n` or `0` according to whether `n ∣ m` (`char_sum`), and the circle mean of a character is
`1` or `0` according to whether `m = 0` (`integral_char`, `circleMean_char`).

This is what makes the periodic trapezoidal rule spectrally accurate for smooth periodic
integrands: if the Fourier coefficients of `F` decay geometrically, the error decays
geometrically in `n` (`error_le_of_decay`). This convergence class is qualitatively different
from the derivative-based bounds `intervalIntegral.trapezoidal_error_le` and
`intervalIntegral.trapezoidal_error_le_of_c2`, which are polynomial in `N` and cannot see
periodicity or analyticity; for periodic analytic integrands the exponential rate is the
standard reason spectral methods exist (see Trefethen & Weideman, *The Exponentially
Convergent Trapezoidal Rule*, SIAM Review 56 (2014)).

## Main definitions

* `PeriodicTrapezoidal.mean n F` : the `n`-point periodic trapezoidal mean of `F`.
* `PeriodicTrapezoidal.circleMean F` : the circle mean `(2 * π)⁻¹ ∫ x in 0..2 * π, F x`.
* `PeriodicTrapezoidal.char m` : the character `x ↦ e^{i m x}`.

## Main statements

* `PeriodicTrapezoidal.char_sum` : `∑_{j < n} e^{2 * π i m j / n} = n` if `n ∣ m`, else `0`.
* `PeriodicTrapezoidal.integral_char` : `∫ x in 0..2 * π, e^{i m x} = 2 * π` if `m = 0`, else `0`.
* `PeriodicTrapezoidal.error_char` : the error functional annihilates every character except
  the aliased nonzero frequencies.
* `PeriodicTrapezoidal.error_le_of_decay` : a geometric error bound
  `M * q ^ n * (2 * K + 1) + 2 * ε` from a decay hypothesis on the first `2 * K + 1` Fourier
  coefficients and `ε`-closeness of `F` to that partial character sum.  The decay hypothesis
  is deliberately left as a hypothesis; it is supplied, for instance, by analyticity of `F` in
  a strip around the real axis.
-/

@[expose] public section

namespace PeriodicTrapezoidal

open MeasureTheory intervalIntegral
open scoped Real

/-! ### The two means and the characters -/

/-- The `n`-point periodic trapezoidal mean on the circle of circumference `2 * π`. -/
noncomputable def mean (n : ℕ) (F : ℝ → ℂ) : ℂ :=
  (1 / (n : ℂ)) * ∑ j ∈ Finset.range n, F (2 * π * (j : ℝ) / (n : ℝ))

/-- The circle mean `(1 / (2 * π)) ∫ x in 0..2 * π, F x`. -/
noncomputable def circleMean (F : ℝ → ℂ) : ℂ :=
  (1 / (2 * (π : ℂ))) * ∫ x in (0 : ℝ)..(2 * π), F x

/-- The character `x ↦ e^{i m x}`. -/
noncomputable def char (m : ℤ) : ℝ → ℂ := fun x => Complex.exp ((m : ℂ) * x * Complex.I)

/-! ### The character sum: the trapezoidal rule is exact on low frequencies

`∑_{j < n} e^{2 * π i m j / n} = n` if `n ∣ m` and `0` otherwise.  This single identity is why
the periodic trapezoidal rule is spectrally accurate: the rule reproduces every character's
mean exactly, so its error is carried entirely by the aliased frequencies `m = n * k`. -/

/-- The geometric character sum: `∑_{j < n} e^{2 * π i m j / n} = n` if `n ∣ m`, else `0`. -/
theorem char_sum (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ j ∈ Finset.range n,
        Complex.exp (2 * (π : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ)))
      = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ω : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I * (m : ℂ) / (n : ℂ)) with hω
  -- every summand is a power of `ω`
  have hterm : ∀ j : ℕ,
      Complex.exp (2 * (π : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ)))
        = ω ^ j := by
    intro j
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  -- `ω ^ n = 1` for every `m`
  have hωn : ω ^ n = 1 := by
    rw [hω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨m, by field_simp⟩
  by_cases hdiv : (n : ℤ) ∣ m
  · -- every term is `1`, so the sum is `n`
    rw [ite_eq_left hdiv]
    obtain ⟨q, hq⟩ := hdiv
    have hone : ∀ j : ℕ, ω ^ j = 1 := by
      intro j
      rw [hω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨q * (j : ℤ), ?_⟩
      rw [hq]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun j _ => hone j]
    simp
  · -- `ω ≠ 1`, so the sum is a geometric series whose ratio is off the root
    rw [ite_eq_right hdiv]
    have hω1 : ω ≠ 1 := by
      intro h
      rw [hω] at h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      have hkey : (n : ℂ) * (k : ℂ) = (m : ℂ) := by
        have hk' := hk
        field_simp at hk'
        exact hk'.symm
      exact hdiv ⟨k, by exact_mod_cast hkey.symm⟩
    rw [geom_sum_eq hω1 n, hωn]
    simp

/-! ### The character's circle mean

`(1 / (2 * π)) ∫_0^{2 * π} e^{i m x} dx = 1` if `m = 0` and `0` otherwise — the fundamental
orthogonality, by the fundamental theorem of calculus with the explicit antiderivative
`e^{i m x} / (i * m)`. -/

/-- The integral of a character over the circle: `2 * π` at frequency `0`, `0` elsewhere. -/
theorem integral_char (m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), char m x
      = if m = 0 then (2 * (π : ℂ)) else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [char]
  · have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero hmC Complex.I_ne_zero
    rw [ite_eq_right hm]
    have hpt : ∀ x : ℝ, char m x = Complex.exp (((m : ℂ) * Complex.I) * (x : ℂ)) := by
      intro x
      simp only [char]
      congr 1
      ring
    simp_rw [hpt]
    rw [integral_exp_mul_complex hc]
    have hz : Complex.exp (((m : ℂ) * Complex.I) * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨m, by push_cast; ring⟩
    rw [hz]
    simp

/-! ### The error functional on characters

Putting the two preceding facts together: `Eₙ (e^{i m x})` is `-1` exactly on the aliased
nonzero frequencies and `0` everywhere else.  This is the whole content of "the trapezoidal
rule is exact on low frequencies". -/

/-- The `n`-point periodic trapezoidal mean of a character is `1` on the multiples of `n`
(including frequency `0`) and `0` elsewhere. -/
theorem mean_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    mean n (char m) = if (n : ℤ) ∣ m then 1 else 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold mean
  have hpt : ∀ j : ℕ, char m (2 * π * (j : ℝ) / (n : ℝ))
      = Complex.exp (2 * (π : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ))) := by
    intro j
    simp only [char]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hpt j, char_sum n hn m]
  by_cases h : (n : ℤ) ∣ m
  · rw [ite_eq_left h, ite_eq_left h]
    field_simp
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- The circle mean of a character is `1` at frequency `0` and `0` elsewhere. -/
theorem circleMean_char (m : ℤ) :
    circleMean (char m) = if m = 0 then 1 else 0 := by
  unfold circleMean
  rw [integral_char m]
  have hpiC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : m = 0
  · rw [ite_eq_left h, ite_eq_left h]
    field_simp
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- **The error functional annihilates every character except the aliased frequencies.** -/
theorem error_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    circleMean (char m) - mean n (char m)
      = if (n : ℤ) ∣ m ∧ m ≠ 0 then (-1 : ℂ) else 0 := by
  rw [circleMean_char m, mean_char n hn m]
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [ite_eq_right hm]
    by_cases h : (n : ℤ) ∣ m
    · rw [ite_eq_left h, ite_eq_left ⟨h, hm⟩]; ring
    · rw [ite_eq_right h, ite_eq_right (fun hc => h hc.1)]; ring

/-! ### The two norm bounds -/

/-- The trapezoidal mean is bounded by the sup norm: a mean of `n` numbers. -/
theorem mean_norm_le (n : ℕ) (hn : 0 < n) {h : ℝ → ℂ} {ε : ℝ}
    (hε : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π), ‖h x‖ ≤ ε) : ‖mean n h‖ ≤ ε := by
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hε 0 ⟨le_rfl, by positivity⟩)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnode : ∀ j ∈ Finset.range n, ‖h (2 * π * (j : ℝ) / (n : ℝ))‖ ≤ ε := by
    intro j hj
    refine hε _ ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hnR]
    have hj' : (j : ℝ) < (n : ℝ) := by exact_mod_cast Finset.mem_range.1 hj
    nlinarith [Real.pi_pos]
  have hsum : ‖∑ j ∈ Finset.range n, h (2 * π * (j : ℝ) / (n : ℝ))‖ ≤ (n : ℝ) * ε := by
    calc ‖∑ j ∈ Finset.range n, h (2 * π * (j : ℝ) / (n : ℝ))‖
        ≤ ∑ j ∈ Finset.range n, ‖h (2 * π * (j : ℝ) / (n : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, ε := Finset.sum_le_sum hnode
      _ = (n : ℝ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]
  unfold mean
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc (1 / (n : ℝ)) * ‖∑ j ∈ Finset.range n, h (2 * π * (j : ℝ) / (n : ℝ))‖
      ≤ (1 / (n : ℝ)) * ((n : ℝ) * ε) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = ε := by field_simp

/-- The circle mean is bounded by the sup norm: the integral is at most length × sup. -/
theorem circleMean_norm_le {h : ℝ → ℂ} {ε : ℝ}
    (hε : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π), ‖h x‖ ≤ ε) : ‖circleMean h‖ ≤ ε := by
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hb : ‖∫ x in (0 : ℝ)..(2 * π), h x‖ ≤ 2 * π * ε := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * π) (C := ε) (f := h) (fun x hx => by
        rw [Set.uIoc_of_le (le_of_lt h2pi)] at hx
        exact hε x ⟨le_of_lt hx.1, hx.2⟩)
    rw [sub_zero, abs_of_pos h2pi] at h
    linarith
  unfold circleMean
  rw [norm_mul]
  have hinv : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hinv]
  calc (1 / (2 * π)) * ‖∫ x in (0 : ℝ)..(2 * π), h x‖
      ≤ (1 / (2 * π)) * (2 * π * ε) := by
        apply mul_le_mul_of_nonneg_left hb; positivity
    _ = ε := by field_simp

/-! ### The error functional on character sums -/

theorem mean_add (n : ℕ) (h₁ h₂ : ℝ → ℂ) :
    mean n (fun x => h₁ x + h₂ x) = mean n h₁ + mean n h₂ := by
  unfold mean
  simp only [Finset.sum_add_distrib]
  ring

theorem mean_smul (n : ℕ) (c : ℂ) (h : ℝ → ℂ) :
    mean n (fun x => c * h x) = c * mean n h := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

theorem circleMean_add {h₁ h₂ : ℝ → ℂ}
    (hi₁ : IntervalIntegrable h₁ volume (0 : ℝ) (2 * π))
    (hi₂ : IntervalIntegrable h₂ volume (0 : ℝ) (2 * π)) :
    circleMean (fun x => h₁ x + h₂ x) = circleMean h₁ + circleMean h₂ := by
  unfold circleMean
  rw [intervalIntegral.integral_add hi₁ hi₂]
  ring

theorem circleMean_smul (c : ℂ) (h : ℝ → ℂ) :
    circleMean (fun x => c * h x) = c * circleMean h := by
  unfold circleMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem mean_sub (n : ℕ) (h₁ h₂ : ℝ → ℂ) :
    mean n (fun x => h₁ x - h₂ x) = mean n h₁ - mean n h₂ := by
  unfold mean
  rw [Finset.sum_sub_distrib]
  ring

theorem circleMean_sub {h₁ h₂ : ℝ → ℂ}
    (hi₁ : IntervalIntegrable h₁ volume (0 : ℝ) (2 * π))
    (hi₂ : IntervalIntegrable h₂ volume (0 : ℝ) (2 * π)) :
    circleMean (fun x => h₁ x - h₂ x) = circleMean h₁ - circleMean h₂ := by
  unfold circleMean
  rw [intervalIntegral.integral_sub hi₁ hi₂]
  ring

theorem mean_finset_sum (n : ℕ) (s : Finset ℤ) (c : ℤ → ℂ) :
    mean n (fun x => ∑ k ∈ s, c k * char k x) = ∑ k ∈ s, c k * mean n (char k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mean]
  | insert a s ha ih =>
    have hfun : (fun x => ∑ k ∈ insert a s, c k * char k x)
        = fun x => c a * char a x + ∑ k ∈ s, c k * char k x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [hfun, mean_add, mean_smul, ih, Finset.sum_insert ha]

theorem circleMean_finset_sum (s : Finset ℤ) (c : ℤ → ℂ) :
    circleMean (fun x => ∑ k ∈ s, c k * char k x) = ∑ k ∈ s, c k * circleMean (char k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleMean]
  | insert a s ha ih =>
    have hfun : (fun x => ∑ k ∈ insert a s, c k * char k x)
        = fun x => c a * char a x + ∑ k ∈ s, c k * char k x := by
      funext x
      rw [Finset.sum_insert ha]
    have hi₁ : IntervalIntegrable (char a) volume (0 : ℝ) (2 * π) := by
      have : Continuous (char a) := by unfold char; fun_prop
      exact this.intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun x => ∑ k ∈ s, c k * char k x) volume (0 : ℝ) (2 * π) := by
      have : Continuous (fun x => ∑ k ∈ s, c k * char k x) := by
        refine continuous_finsetSum _ fun k _ => ?_
        unfold char; fun_prop
      exact this.intervalIntegrable _ _
    rw [hfun, circleMean_add (by simpa using hi₁.const_mul (c a)) hi₂, circleMean_smul, ih,
      Finset.sum_insert ha]

/-! ### The spectral error bound

`Eₙ = circleMean - mean` is additive and `ℂ`-homogeneous, so on a finite character sum it is
the sum of its values on the characters (`error_char`), which vanish off the aliased
frequencies.  What remains is a `q ^ n` factor from the decay hypothesis on the Fourier
coefficients and a cardinality factor from the number of characters that can alias — which
is exactly the `M * q ^ n * (2 * K + 1)` of the bound below. -/

/-- **Geometric accuracy of the periodic trapezoidal rule.**  If `F` is `ε`-close, uniformly
on `[0, 2 * π]`, to the partial character sum `∑_{|k| ≤ K} cₖ e^{i k x}` whose nonzero
coefficients satisfy `‖cₖ‖ ≤ M * q ^ {|k|}` for some `q < 1`, then the error of the
`n`-point periodic trapezoidal rule is at most `M * q ^ n * (2 * K + 1) + 2 * ε`.

The decay hypothesis is deliberately left abstract: it holds, for example, when `F`
extends to a function that is holomorphic and bounded in a strip around the real axis
(the coefficients then decay like `e ^ (- a * |k|)`), which is the setting in which the
exponential convergence of the periodic trapezoidal rule is classically used. -/
theorem error_le_of_decay
    {F : ℝ → ℂ} {c : ℤ → ℂ} {M q ε : ℝ} {K n : ℕ}
    (hn : 0 < n) (hM : 0 ≤ M) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hFint : IntervalIntegrable F volume (0 : ℝ) (2 * π))
    (hdecay : ∀ k : ℤ, k ≠ 0 → ‖c k‖ ≤ M * q ^ k.natAbs)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖F x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), c k * char k x‖ ≤ ε) :
    ‖circleMean F - mean n F‖ ≤ M * q ^ n * (2 * (K : ℝ) + 1) + 2 * ε := by
  classical
  set S : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hS
  set P : ℝ → ℂ := fun x => ∑ k ∈ S, c k * char k x with hP
  -- `P` is continuous, hence interval-integrable
  have hPint : IntervalIntegrable P volume (0 : ℝ) (2 * π) := by
    have hc : Continuous P := by
      rw [hP]
      exact continuous_finsetSum _ fun k _ => by unfold char; fun_prop
    exact hc.intervalIntegrable _ _
  -- the tail: `F` and `P` are pointwise `ε`-close
  have hclose : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π), ‖(F - P) x‖ ≤ ε := by
    intro x hx
    simpa [hP, hS, Pi.sub_apply] using happrox x hx
  -- the aliasing bound on `P`
  have hEP : circleMean P - mean n P
      = ∑ k ∈ S, c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0) := by
    rw [hP, circleMean_finset_sum, mean_finset_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      have h := error_char n hn k
      linear_combination c k * h
  have hcard : (S.card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
    have hN : S.card ≤ 2 * K + 1 := by
      rw [hS, Int.card_Icc]
      have hle : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hle, Int.toNat_natCast]
    calc (S.card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast hN
      _ = 2 * (K : ℝ) + 1 := by push_cast; ring
  -- each aliased frequency carries `q ^ {|k|} ≤ q ^ n`; the rest carry nothing
  have hterm : ∀ k ∈ S, ‖c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0)‖ ≤ M * q ^ n := by
    intro k _
    by_cases hk : (n : ℤ) ∣ k ∧ k ≠ 0
    · have hkn : n ≤ k.natAbs := by
        obtain ⟨j, rfl⟩ := hk.1
        have hj : j ≠ 0 := fun h0 => hk.2 (by rw [h0, mul_zero])
        have hj1 : 1 ≤ j.natAbs := by have := Int.natAbs_pos.mpr hj; omega
        rw [Int.natAbs_mul]
        simp only [Int.natAbs_natCast]
        calc n = n * 1 := by ring
          _ ≤ n * j.natAbs := Nat.mul_le_mul_left n hj1
      simp only [ite_eq_left hk]
      rw [show c k * (-1 : ℂ) = -c k by ring, norm_neg]
      refine le_trans (hdecay k hk.2) (mul_le_mul_of_nonneg_left ?_ hM)
      exact pow_le_pow_of_le_one hq0 hq1.le hkn
    · simp only [ite_eq_right hk, mul_zero, norm_zero]
      exact mul_nonneg hM (pow_nonneg hq0 n)
  have hPbound : ‖circleMean P - mean n P‖ ≤ M * q ^ n * (2 * (K : ℝ) + 1) := by
    rw [hEP]
    calc ‖∑ k ∈ S, c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0)‖
        ≤ ∑ k ∈ S, ‖c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ S, M * q ^ n := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (M * q ^ n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (K : ℝ) + 1) * (M * q ^ n) := by
          apply mul_le_mul_of_nonneg_right hcard
          exact mul_nonneg hM (pow_nonneg hq0 n)
      _ = M * q ^ n * (2 * (K : ℝ) + 1) := by ring
  -- reassemble
  have hsplit : circleMean F - mean n F
      = (circleMean (F - P) - mean n (F - P)) + (circleMean P - mean n P) := by
    have h1 : circleMean (F - P) = circleMean F - circleMean P := by
      exact circleMean_sub (h₁ := F) (h₂ := P) hFint hPint
    have h2 : mean n (F - P) = mean n F - mean n P := by
      exact mean_sub n F P
    rw [h1, h2]
    ring
  rw [hsplit]
  have htail : ‖circleMean (F - P) - mean n (F - P)‖ ≤ 2 * ε := by
    have h1 : ‖circleMean (F - P)‖ ≤ ε := circleMean_norm_le hclose
    have h2 : ‖mean n (F - P)‖ ≤ ε := mean_norm_le n hn hclose
    calc ‖circleMean (F - P) - mean n (F - P)‖
        ≤ ‖circleMean (F - P)‖ + ‖mean n (F - P)‖ := norm_sub_le _ _
      _ ≤ ε + ε := add_le_add h1 h2
      _ = 2 * ε := by ring
  calc ‖(circleMean (F - P) - mean n (F - P)) + (circleMean P - mean n P)‖
      ≤ ‖circleMean (F - P) - mean n (F - P)‖ + ‖circleMean P - mean n P‖ :=
        norm_add_le _ _
    _ ≤ 2 * ε + M * q ^ n * (2 * (K : ℝ) + 1) := add_le_add htail hPbound
    _ = M * q ^ n * (2 * (K : ℝ) + 1) + 2 * ε := by ring

end PeriodicTrapezoidal
