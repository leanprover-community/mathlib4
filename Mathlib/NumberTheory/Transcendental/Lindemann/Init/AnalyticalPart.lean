/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# The Lindemann-Weierstrass theorem
-/

namespace LindemannWeierstrass

noncomputable section

open scoped Nat

open Complex Polynomial

attribute [local fun_prop] Polynomial.differentiable Complex.continuous_abs

theorem hasDerivAt_cexp_mul_sumIDeriv (p : ℂ[X]) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * p.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert (h₁.mul h₂).neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

theorem integral_exp_mul_eval (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in (0)..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

private def P (p : ℂ[X]) (s : ℂ) :=
  exp s * p.sumIDeriv.eval 0 - p.sumIDeriv.eval s

private theorem P_eq_integral_exp_mul_eval (p : ℂ[X]) (s : ℂ) :
    P p s = exp s * (s * ∫ x in (0)..1, exp (-(x • s)) * p.eval (x • s)) := by
  rw [integral_exp_mul_eval, mul_add, mul_neg, exp_neg, mul_inv_cancel_left₀ (exp_ne_zero s),
    neg_add_eq_sub, P]

/--
Given a sequence of complex polynomials `p(q)`, a complex constant `s`, and a real constant `c` such
that `|p(q)(xs)| ≤ c ^ q` for all `q ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a nonnegative
constant `c'` such that for all nonzero `q ∈ ℕ`, `|P(p(q), s)| ≤ c' ^ q`.
-/
private theorem P_le_aux (p : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ q : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c' ≥ 0, ∀ q : ℕ,
      Complex.abs (P (p q) s) ≤
        Real.exp s.re * (Real.exp (Complex.abs s) * c' ^ q * (Complex.abs s)) := by
  refine ⟨|c|, abs_nonneg _, fun q => ?_⟩
  rw [P_eq_integral_exp_mul_eval (p q) s, mul_comm s, map_mul, map_mul, abs_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← norm_eq_abs, ← mul_one (_ * _)]
  convert MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ _ _
  · rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  · exact measurableSet_Ioc
  intro x hx
  rw [norm_mul, norm_eq_abs, abs_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_abs _).trans
    rw [← norm_eq_abs, ← norm_eq_abs, norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← _root_.abs_pow, norm_eq_abs]
    exact (hc q x hx).trans (le_abs_self _)

/--
Given a sequence of complex polynomials `p(q)`, a complex constant `s`, and a real constant `c` such
that `|p(q)(xs)| ≤ c ^ q` for all `q ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a nonnegative
constant `c'` such that for all nonzero `q ∈ ℕ`, `|P(p(q), s)| ≤ c' ^ q`.
-/
private theorem P_le (p : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ q : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c' ≥ 0, ∀ q ≠ 0, Complex.abs (P (p q) s) ≤ c' ^ q := by
  obtain ⟨c', hc', h'⟩ := P_le_aux p s c hc; clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp (Complex.abs s)) 1
  let c₃ := max (Complex.abs s) 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro q hq
  refine (h' q).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : ℝ} : x ≤ max x 1 ^ q :=
    (max_cases x 1).elim (fun h ↦ h.1.symm ▸ le_self_pow₀ h.2 hq)
      fun h ↦ by rw [h.1, one_pow]; exact h.2.le
  gcongr <;> exact le_max_one_pow

/--
Given a polynomial with integer coefficients `p` and a complex constant `s`, there is a nonnegative
`c` such that for all nonzero `q ∈ ℕ`, `|P(X ^ (q - 1) * p ^ q, s)| ≤ c ^ q`.

Note: Jacobson writes `h(x)` for `x ^ (q - 1) * p(x) ^ q` and `bⱼ` for its coefficients.
-/
private theorem exp_polynomial_approx_aux (p : ℤ[X]) (s : ℂ) :
    ∃ c ≥ 0,
      ∀ q ≠ 0, Complex.abs (P (map (algebraMap ℤ ℂ) (X ^ (q - 1) * p ^ q)) s) ≤ c ^ q := by
  have : Bornology.IsBounded
      ((fun x : ℝ ↦ max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) '' Set.Ioc 0 1) := by
    have h :
      (fun x : ℝ ↦ max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) '' Set.Ioc 0 1 ⊆
        (fun x : ℝ ↦ max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) '' Set.Icc 0 1 :=
      Set.image_subset _ Set.Ioc_subset_Icc_self
    refine (IsCompact.image isCompact_Icc ?_).isBounded.subset h
    fun_prop
  obtain ⟨c, h⟩ := this.exists_norm_le
  simp_rw [Real.norm_eq_abs] at h
  refine P_le _ s c (fun q x hx => ?_)
  specialize h (max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) (Set.mem_image_of_mem _ hx)
  refine le_trans ?_ (pow_le_pow_left₀ (abs_nonneg _) h _)
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
    Complex.abs_pow, real_smul, map_mul, abs_ofReal, ← eval₂_eq_eval_map, ← aeval_def, abs_mul,
    Complex.abs_abs, mul_pow, abs_of_pos hx.1]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Complex.abs.nonneg _) _)
  rw [← mul_pow, _root_.abs_of_nonneg (by positivity), max_def]
  split_ifs with hx1
  · rw [one_pow]
    exact pow_le_one₀ (mul_nonneg hx.1.le (Complex.abs.nonneg _)) hx1
  · push_neg at hx1
    exact pow_le_pow_right₀ hx1.le (Nat.sub_le _ _)

/--
See equation (68), page 285 of [Jacobson, *Basic Algebra I, 4.12*][jacobson1974].

Given a polynomial `p` with integer coefficients, we can find a constant `c : ℝ` and for each prime
`q > |p₀|`, `n(q) : ℤ` and `g(q) : ℤ[X]` such that

* `q` does not divide `n(q)`
* `deg(g(q)) < q * deg(p)`
* all complex roots `r` of `p` satisfy `|n(q) * e ^ r - q * g(q)(r)| ≤ c ^ q / (q - 1)!`

In the proof of Lindemann-Weierstrass, we will take `p` to be a polynomial whose complex roots
are the algebraic numbers whose exponentials we want to prove to be linearly independent.

Note: Jacobson writes `f` for our `p`, `p` for our `q`, `N_p` for our `n(q)`, `g_p` for our `g(q)`
and `M` for our `c` (modulo a constant factor).
-/
theorem exp_polynomial_approx (p : ℤ[X]) (hp : p.eval 0 ≠ 0) :
    ∃ c,
      ∀ q > (eval 0 p).natAbs, q.Prime →
        ∃ n : ℤ, ¬ ↑q ∣ n ∧ ∃ gq : ℤ[X], gq.natDegree ≤ q * p.natDegree - 1 ∧
          ∀ {r : ℂ}, r ∈ p.aroots ℂ →
            Complex.abs (n • exp r - q • aeval r gq : ℂ) ≤ c ^ q / (q - 1)! := by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' c'0 Pp'_le using exp_polynomial_approx_aux p
  use
    if h : ((p.aroots ℂ).map c').toFinset.Nonempty then ((p.aroots ℂ).map c').toFinset.max' h else 0
  intro q q_gt prime_q
  obtain ⟨gq', -, h'⟩ := eval_sumIDeriv_of_pos (X ^ (q - 1) * p ^ q) prime_q.pos
  specialize h' 0 (by rw [C_0, sub_zero])
  use p.eval 0 ^ q + q * gq'.eval 0
  constructor
  · rw [dvd_add_left (dvd_mul_right _ _)]
    contrapose! q_gt with h
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hp) (Int.natCast_dvd.mp (Int.Prime.dvd_pow' prime_q h))
  obtain ⟨gq, gq'_le, h⟩ := aeval_sumIDeriv ℂ (X ^ (q - 1) * p ^ q) q
  refine ⟨gq, ?_, ?_⟩
  · refine gq'_le.trans ((tsub_le_tsub_right natDegree_mul_le q).trans ?_)
    rw [natDegree_X_pow, natDegree_pow, tsub_add_eq_add_tsub prime_q.one_le, tsub_right_comm,
      add_tsub_cancel_left]
  intro r hr
  specialize h r _
  · rw [mem_roots'] at hr
    rw [Polynomial.map_mul, p.map_pow]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hr.2) _) _
  rw [nsmul_eq_mul] at h
  have :
      (↑(eval 0 p ^ q + q * eval 0 gq') * cexp r - q * (aeval r) gq) * (q - 1)! =
      ((eval 0 p ^ q * cexp r) * (q - 1)! +
        ↑(q * (q - 1)!) * (eval 0 gq' * cexp r - (aeval r) gq)) := by
    push_cast; ring
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← abs_natCast, ← map_mul,
    this, Nat.mul_factorial_pred prime_q.pos, mul_sub, ← h]
  have :
      ↑(eval 0 p) ^ q * cexp r * ↑(q - 1)! +
        (↑q ! * (↑(eval 0 gq') * cexp r) - (aeval r) (sumIDeriv (X ^ (q - 1) * p ^ q))) =
      ((q - 1)! • ↑(eval 0 (p ^ q)) + q ! • ↑(eval 0 gq') : ℤ) * cexp r -
        (aeval r) (sumIDeriv (X ^ (q - 1) * p ^ q)) := by
    simp; ring
  rw [this, ← h', mul_comm, ← eq_intCast (algebraMap ℤ ℂ),
    ← aeval_algebraMap_apply_eq_algebraMap_eval, map_zero,
    aeval_sumIDeriv_eq_eval, aeval_sumIDeriv_eq_eval, ← P]
  refine (Pp'_le r q prime_q.ne_zero).trans (pow_le_pow_left₀ (c'0 r) ?_ _)
  have aux : c' r ∈ (Multiset.map c' (p.aroots ℂ)).toFinset := by
    simpa only [Multiset.mem_toFinset] using Multiset.mem_map_of_mem _ hr
  have h : ((p.aroots ℂ).map c').toFinset.Nonempty := ⟨c' r, aux⟩
  simpa only [h, ↓reduceDIte] using Finset.le_max' _ _ aux

end

end LindemannWeierstrass
