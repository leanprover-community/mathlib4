/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Analytic part of the Lindemann-Weierstrass theorem

The proof is partially based on [Jacobson, *Basic Algebra I, 4.12*][jacobson1974].
-/

namespace LindemannWeierstrass

noncomputable section

open scoped Nat
open Complex Polynomial

theorem hasDerivAt_cexp_mul_sumIDeriv (p : ℂ[X]) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * p.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

theorem integral_exp_mul_eval (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in 0..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

/--
In what follows, we will use integration by parts to rewrite provide an integral form for `P`
(`P_eq_integral_exp_mul_eval`) and under some hypotheses find a bound `|P(fₚ, s)| ≤ c' ^ p` for a
sequence of polynomials `fₚ` (`P_le`). We will then apply this to `fₚ := X ^ (p - 1) * f ^ p` for
any `f : ℤ[X]` and `p ≠ 0` (`exp_polynomial_approx_aux`) and this will be exactly the bound we need
in `exp_polynomial_approx`.

This approach is based on
[the wikipedia proof](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstrass_theorem):
`Iᵢ(s) = P(fᵢ, s)`. Jacobson finds a slightly different bound using the power series of `eˣ`.
-/
private def P (f : ℂ[X]) (s : ℂ) :=
  exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s

private theorem P_eq_integral_exp_mul_eval (f : ℂ[X]) (s : ℂ) :
    P f s = exp s * (s * ∫ x in 0..1, exp (-(x • s)) * f.eval (x • s)) := by
  rw [integral_exp_mul_eval, mul_add, mul_neg, exp_neg, mul_inv_cancel_left₀ (exp_ne_zero s),
    neg_add_eq_sub, P]

private theorem P_algebraMap (f : ℤ[X]) (s : ℂ) :
    P (f.map <| algebraMap ℤ ℂ) s = exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.aeval s := by
  simp [P, aeval_sumIDeriv_eq_eval]

/--
Given a sequence of complex polynomials `fₚ`, a complex constant `s`, and a real constant `c` such
that `|fₚ(xs)| ≤ c ^ p` for all `p ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a nonnegative
constant `c'` such that for all nonzero `p ∈ ℕ`, `|P(fₚ, s)| ≤ c' ^ p`.
-/
private theorem P_le_aux (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p : ℕ,
      ‖P (f p) s‖ ≤
        Real.exp s.re * (Real.exp ‖s‖ * c' ^ p * ‖s‖) := by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

/--
Given a sequence of complex polynomials `fₚ`, a complex constant `s`, and a real constant `c` such
that `|fₚ(xs)| ≤ c ^ p` for all `p ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a nonnegative
constant `c'` such that for all nonzero `p ∈ ℕ`, `|P(fₚ, s)| ≤ c' ^ p`.
-/
private theorem P_le (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p ≠ 0, ‖P (f p) s‖ ≤ c' ^ p := by
  obtain ⟨c', hc', h'⟩ := P_le_aux f s c hc; clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro p hp
  refine (h' p).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : ℝ} : x ≤ max x 1 ^ p :=
    (max_cases x 1).elim (fun h ↦ h.1.symm ▸ le_self_pow₀ h.2 hp)
      fun h ↦ by rw [h.1, one_pow]; exact h.2.le
  gcongr <;> exact le_max_one_pow

/--
Given a polynomial with integer coefficients `p` and a complex constant `s`, there is a nonnegative
`c` such that for all nonzero `q ∈ ℕ`, `|P(X ^ (q - 1) * p ^ q, s)| ≤ c ^ q`.

Note: Jacobson writes `h(x)` for `x ^ (q - 1) * p(x) ^ q` and `bⱼ` for its coefficients.
-/
private theorem exp_polynomial_approx_aux (f : ℤ[X]) (s : ℂ) :
    ∃ c ≥ 0, ∀ p ≠ 0, ‖P (map (algebraMap ℤ ℂ) (X ^ (p - 1) * f ^ p)) s‖ ≤ c ^ p := by
  have : Bornology.IsBounded
      ((fun x : ℝ ↦ max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1) := by
    have h :
      (fun x : ℝ ↦ max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1 ⊆
        (fun x : ℝ ↦ max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Icc 0 1 :=
      Set.image_mono Set.Ioc_subset_Icc_self
    refine (IsCompact.image isCompact_Icc ?_).isBounded.subset h
    fun_prop
  obtain ⟨c, h⟩ := this.exists_norm_le
  simp_rw [Real.norm_eq_abs] at h
  refine P_le _ s c (fun p x hx => ?_)
  specialize h (max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) (Set.mem_image_of_mem _ hx)
  grw [← h]
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, norm_mul,
    Complex.norm_pow, real_smul, norm_mul, norm_real, eval_map_algebraMap, abs_mul,
    abs_norm, mul_pow, Real.norm_of_nonneg hx.1.le]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
  rw [← mul_pow, abs_of_nonneg (by positivity), max_def]
  split_ifs with hx1
  · rw [one_pow]
    exact pow_le_one₀ (mul_nonneg hx.1.le (norm_nonneg _)) hx1
  · push_neg at hx1
    exact pow_le_pow_right₀ hx1.le (Nat.sub_le _ _)

/--
Given a polynomial `f` with integer coefficients, we can find a constant `c : ℝ` and for each prime
`p > |f₀|`, `nₚ : ℤ` and `gₚ : ℤ[X]` such that

* `p` does not divide `nₚ`
* `deg(gₚ) < p * deg(f)`
* all complex roots `r` of `f` satisfy `|nₚ * e ^ r - p * gₚ(r)| ≤ c ^ p / (p - 1)!`

In the proof of Lindemann-Weierstrass, we will take `f` to be a polynomial whose complex roots
are the algebraic numbers whose exponentials we want to prove to be linearly independent.

Note: Jacobson (equation (68), page 285) writes `Nₚ` for our `nₚ` and `M` for our `c` (modulo a
constant factor).
-/
theorem exp_polynomial_approx (f : ℤ[X]) (hf : f.eval 0 ≠ 0) :
    ∃ c,
      ∀ p > (eval 0 f).natAbs, p.Prime →
        ∃ nₚ : ℤ, ¬ ↑p ∣ nₚ ∧ ∃ gₚ : ℤ[X], gₚ.natDegree ≤ p * f.natDegree - 1 ∧
          ∀ {r : ℂ}, r ∈ f.aroots ℂ →
            ‖nₚ • exp r - p • aeval r gₚ‖ ≤ c ^ p / (p - 1)! := by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' c'0 abs_P_le using exp_polynomial_approx_aux f
  by_cases h : f.aroots ℂ = 0
  · refine ⟨0, fun p _ pp => ⟨p + 1, ?_, 0, ?_⟩⟩ <;> simp [pp.ne_one, Int.natCast_dvd, h]
  replace h : ((f.aroots ℂ).map c').toFinset.Nonempty := by simpa
  refine ⟨((f.aroots ℂ).map c').toFinset.max' h, fun p p_gt prime_p => ?_⟩
  let h := X ^ (p - 1) * f ^ p
  obtain ⟨gₚ', -, gₚ'_eq⟩ := eval_sumIDeriv_of_pos h prime_p.pos
  refine ⟨f.eval 0 ^ p + p * gₚ'.eval 0, ?_, ?_⟩
  · rw [dvd_add_left (dvd_mul_right _ _)]
    contrapose! p_gt with h
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hf) (Int.natCast_dvd.mp (Int.Prime.dvd_pow' prime_p h))
  obtain ⟨gₚ, gₚ_le, gₚ_eq⟩ := aeval_sumIDeriv ℂ h p
  refine ⟨gₚ, ?_, ?_⟩
  · refine gₚ_le.trans ((tsub_le_tsub_right natDegree_mul_le p).trans ?_)
    rw [natDegree_X_pow, natDegree_pow, tsub_add_eq_add_tsub prime_p.one_le, tsub_right_comm,
      add_tsub_cancel_left]
  intro r hr
  rw [le_div_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _)]
  calc ↑(p - 1)! * ‖↑(eval 0 f ^ p + ↑p * eval 0 gₚ') * cexp r - ↑p * (aeval r) gₚ‖
    _ = ‖↑(p - 1)! * (↑(eval 0 f ^ p + ↑p * eval 0 gₚ') * cexp r - ↑p * (aeval r) gₚ)‖ := ?_
    _ = ‖(↑(p - 1)! * eval 0 f ^ p + ↑p ! * eval 0 gₚ') * cexp r - ↑p ! * (aeval r) gₚ‖ := ?_
    _ = ‖P (map (algebraMap ℤ ℂ) h) r‖ := ?_
    _ ≤ c' r ^ p := abs_P_le r p prime_p.ne_zero
    _ ≤ _ := pow_le_pow_left₀ (c'0 r) ?_ _
  · rw [norm_mul, norm_natCast]
  · rw [← Nat.mul_factorial_pred prime_p.ne_zero]
    push_cast
    ring_nf
  · specialize gₚ_eq r _
    · rw [mem_roots'] at hr
      rw [Polynomial.map_mul, f.map_pow]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hr.2) _) _
    specialize gₚ'_eq 0 (by rw [C_0, sub_zero])
    simp_rw [nsmul_eq_mul] at gₚ_eq gₚ'_eq
    rw [P_algebraMap, gₚ_eq, gₚ'_eq, eval_pow]
    push_cast
    ring_nf
  · apply Finset.le_max'
    simpa using Multiset.mem_map_of_mem _ hr

end

end LindemannWeierstrass
