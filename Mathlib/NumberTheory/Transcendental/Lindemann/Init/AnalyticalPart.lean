/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# The Lindemann-Weierstrass theorem
-/

namespace LindemannWeierstrass

noncomputable section

open scoped Nat

open Complex Polynomial

attribute [local fun_prop] Polynomial.differentiable Differentiable.cexp Complex.continuous_abs

set_option linter.style.multiGoal false in
theorem deriv_cexp_mul_sumIDeriv (p : ℂ[X]) (s : ℂ) :
    (deriv fun x ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s))) =
      fun x : ℝ ↦ s * (cexp (-(x • s)) * p.eval (x • s)) := by
  funext x
  have h₁ : (fun y : ℝ ↦ p.sumIDeriv.eval (y • s)) = p.sumIDeriv.eval ∘ (· • s) := rfl
  have h₂ :
    s * p.sumIDeriv.eval (x • s) - (derivative (R := ℂ) (sumIDeriv p)).eval (x • s) * s =
      s * p.eval (x • s) := by
    nth_rw 1 [sumIDeriv_eq_self_add, sumIDeriv_derivative]
    rw [mul_comm _ s, eval_add, mul_add, add_sub_cancel_right]
  rw [deriv.neg, deriv_mul, deriv_cexp, deriv.neg, deriv_smul_const, deriv_id'', h₁, deriv_comp,
    Polynomial.deriv, deriv_smul_const, deriv_id'', one_smul, mul_assoc, ← mul_add, ← mul_neg,
    neg_add', neg_mul, neg_neg, h₂, mul_left_comm]
  on_goal 7 =>
    rw [h₁]
    have : Differentiable ℂ fun x ↦ eval x (sumIDeriv p) := by fun_prop
    apply (this.restrictScalars ℝ).comp
  all_goals fun_prop

theorem integral_exp_mul_eval (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in (0)..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) - -p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1)
      (fun x : ℝ ↦ -(exp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (deriv_cexp_mul_sumIDeriv p s) ?_ (by fun_prop)]
  · simp
  intro x _
  apply (Differentiable.mul _ _).neg.differentiableAt
  · have : Differentiable ℂ fun c ↦ exp (-(c * s)) := by fun_prop
    exact ((this.restrictScalars ℝ).comp ofRealCLM.differentiable : )
  · have : Differentiable ℂ fun x ↦ eval x (sumIDeriv p) := by fun_prop
    apply (this.restrictScalars ℝ).comp <| by fun_prop

def P (p : ℂ[X]) (s : ℂ) :=
  exp s * p.sumIDeriv.eval 0 - p.sumIDeriv.eval s

theorem P_le_aux (p : ℕ → ℂ[X]) (s : ℂ)
    (h : ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1, Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q : ℕ,
      Complex.abs (P (p q) s) ≤
        Real.exp s.re * (Real.exp (Complex.abs s) * c ^ q * (Complex.abs s)) := by
  simp_rw [P]; cases' h with c hc; replace hc := fun q x hx ↦ (hc q x hx).trans (le_abs_self _)
  simp_rw [_root_.abs_pow] at hc; use |c|, abs_nonneg _; intro q
  have h := integral_exp_mul_eval (p q) s
  rw [← mul_right_inj' (exp_ne_zero s), neg_sub_neg, mul_sub, ← mul_assoc _ (exp _), ← exp_add,
    add_neg_cancel, exp_zero, one_mul] at h
  replace h := congr_arg Complex.abs h
  simp_rw [map_mul, abs_exp] at h
  rw [← h, mul_le_mul_left (Real.exp_pos _), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Complex.abs.nonneg _)
  rw [intervalIntegral.integral_of_le zero_le_one, ← Complex.norm_eq_abs, ← mul_one (_ * _)]
  clear h
  convert MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ _ _
  · rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  · exact measurableSet_Ioc
  intro x hx; rw [norm_mul]; refine mul_le_mul ?_ (hc q x hx) (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_eq_abs, abs_exp, Real.exp_le_exp]; apply (re_le_abs _).trans;
  rw [← norm_eq_abs, norm_neg, norm_smul, norm_eq_abs, Real.norm_of_nonneg hx.1.le]
  exact mul_le_of_le_one_left (Complex.abs.nonneg _) hx.2

theorem P_le (p : ℕ → ℂ[X]) (s : ℂ)
    (h : ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1, Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q ≥ 1, Complex.abs (P (p q) s) ≤ c ^ q := by
  obtain ⟨c', hc', h'⟩ := P_le_aux p s h; clear h
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp (Complex.abs s)) 1
  let c₃ := max (Complex.abs s) 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro q hq; refine (h' q).trans ?_; simp_rw [mul_pow]
  have le_max_one_pow : ∀ {x : ℝ}, x ≤ max x 1 ^ q := fun {x} ↦
    (max_cases x 1).elim (fun h ↦ h.1.symm ▸ le_self_pow₀ h.2 (zero_lt_one.trans_le hq).ne')
      fun h ↦ by rw [h.1, one_pow]; exact h.2.le
  gcongr
  all_goals exact le_max_one_pow

open Polynomial

theorem exp_polynomial_approx (p : ℤ[X]) (hp : p.eval 0 ≠ 0) :
    ∃ c,
      ∀ q > (eval 0 p).natAbs, q.Prime →
        ∃ (n : ℤ) (_ : ¬ ↑q ∣ n) (gp : ℤ[X]) (_ : gp.natDegree ≤ q * p.natDegree - 1),
          ∀ {r : ℂ}, r ∈ p.aroots ℂ →
            Complex.abs (n • exp r - q • aeval r gp : ℂ) ≤ c ^ q / (q - 1)! := by
  let p' q := (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ)
  have : ∀ s : ℂ, ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      Complex.abs ((p' q).eval (x • s)) ≤ c ^ q := by
    intro s; dsimp only [p']
    simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
      Complex.abs_pow, real_smul, map_mul, abs_ofReal, ← eval₂_eq_eval_map, ← aeval_def]
    have : Bornology.IsBounded
        ((fun x : ℝ ↦ max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) '' Set.Ioc 0 1) := by
      have h :
        (fun x : ℝ ↦ max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) '' Set.Ioc 0 1 ⊆
          (fun x : ℝ ↦ max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) '' Set.Icc 0 1 :=
        Set.image_subset _ Set.Ioc_subset_Icc_self
      refine (IsCompact.image isCompact_Icc ?_).isBounded.subset h
      fun_prop
    cases' this.exists_norm_le with c h
    use c; intro q x hx
    specialize h (max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) (Set.mem_image_of_mem _ hx)
    refine le_trans ?_ (pow_le_pow_left₀ (norm_nonneg _) h _)
    simp_rw [norm_mul, Real.norm_eq_abs, Complex.abs_abs, mul_pow, abs_of_pos hx.1]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Complex.abs.nonneg _) _)
    rw [max_def]; split_ifs with hx1
    · rw [abs_one, one_pow, ← mul_pow]
      exact pow_le_one₀ (mul_nonneg hx.1.le (Complex.abs.nonneg _)) hx1
    · push_neg at hx1
      rw [abs_mul, Complex.abs_abs, ← mul_pow, abs_of_pos hx.1]
      exact pow_le_pow_right₀ hx1.le (Nat.sub_le _ _)
  choose c' c'0 Pp'_le using fun r ↦ P_le p' r (this r)
  let c :=
    if h : ((p.aroots ℂ).map c').toFinset.Nonempty then ((p.aroots ℂ).map c').toFinset.max' h else 0
  have hc : ∀ x ∈ p.aroots ℂ, c' x ≤ c := by
    intro x hx; dsimp only [c]
    have aux : c' x ∈ (Multiset.map c' (p.aroots ℂ)).toFinset := by
      simpa only [Multiset.mem_toFinset] using Multiset.mem_map_of_mem _ hx
    have h : ((p.aroots ℂ).map c').toFinset.Nonempty := ⟨c' x, aux⟩
    simpa only [h, ↓reduceDIte, ge_iff_le] using Finset.le_max' _ _ aux
  use c
  intro q q_gt prime_q
  have q0 : 0 < q := Nat.Prime.pos prime_q
  obtain ⟨gp', -, h'⟩ := aeval_sumIDeriv_of_pos ℤ (X ^ (q - 1) * p ^ q) q0 Function.injective_id
  simp? [-nsmul_eq_mul] at h' says
    simp only [Algebra.id.map_eq_id, Polynomial.map_mul, Polynomial.map_pow, map_X, map_id,
      eq_intCast, coe_aeval_eq_eval] at h'
  specialize h' 0 (by rw [Int.cast_zero, sub_zero])
  use p.eval 0 ^ q + q • aeval (0 : ℤ) gp'
  rw [exists_prop]
  constructor
  · rw [nsmul_eq_mul, dvd_add_left (dvd_mul_right _ _)]
    intro h
    replace h := Int.Prime.dvd_pow' prime_q h; rw [Int.natCast_dvd] at h
    replace h := Nat.le_of_dvd (Int.natAbs_pos.mpr hp) h
    revert h; rwa [imp_false, not_le]
  obtain ⟨gp, gp'_le, h⟩ := aeval_sumIDeriv ℂ (X ^ (q - 1) * p ^ q) q
  refine ⟨gp, ?_, ?_⟩
  · refine gp'_le.trans ((tsub_le_tsub_right natDegree_mul_le q).trans ?_)
    rw [natDegree_X_pow, natDegree_pow, tsub_add_eq_add_tsub (Nat.one_le_of_lt q0),
      tsub_right_comm]
    apply tsub_le_tsub_right; rw [add_tsub_cancel_left]
  intro r hr
  specialize h r _
  · rw [mem_roots'] at hr
    rw [Polynomial.map_mul, p.map_pow]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hr.2) _) _
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← abs_natCast, ← map_mul,
    mul_comm, mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul, mul_comm,
    Nat.mul_factorial_pred q0, ← h]
  rw [nsmul_eq_mul, ← Int.cast_natCast, ← zsmul_eq_mul, smul_smul, mul_add, ← nsmul_eq_mul, ←
    nsmul_eq_mul, smul_smul, mul_comm, Nat.mul_factorial_pred q0, coe_aeval_eq_eval, ← eval_pow,
    ← h', zsmul_eq_mul, mul_comm, ← eq_intCast (algebraMap ℤ ℂ), eval, hom_eval₂, RingHom.comp_id,
    map_zero, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, ← sumIDeriv_map, ← P]
  exact (Pp'_le r q (Nat.one_le_of_lt q0)).trans (pow_le_pow_left₀ (c'0 r) (hc r hr) _)

end

end LindemannWeierstrass
