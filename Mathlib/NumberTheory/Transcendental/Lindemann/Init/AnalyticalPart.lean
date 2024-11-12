/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Lindemann-Weierstrass theorem
-/

noncomputable section

open scoped Nat

open Complex Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

theorem DifferentiableAt.real_of_complex {e : ℂ → ℂ} {z : ℝ} (h : DifferentiableAt ℂ e ↑z) :
    DifferentiableAt ℝ (fun x : ℝ => e ↑x) z :=
  (h.restrictScalars ℝ).comp z ofRealCLM.differentiable.differentiableAt

theorem Differentiable.real_of_complex {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ fun x : ℝ => e ↑x :=
  (h.restrictScalars ℝ).comp ofRealCLM.differentiable

attribute [fun_prop] Polynomial.differentiable Differentiable.cexp Complex.continuous_abs

set_option linter.style.multiGoal false in
theorem deriv_eq_f (p : ℂ[X]) (s : ℂ) :
    (deriv fun x ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s))) =
      fun x : ℝ ↦ s * (cexp (-(x • s)) * p.eval (x • s)) := by
  have h :
    (fun y : ℝ => p.sumIDeriv.eval (y • s)) =
      (fun x => p.sumIDeriv.eval x) ∘ fun y => y • s :=
    rfl
  funext x
  rw [deriv.neg, deriv_mul, deriv_cexp, deriv.neg]
  any_goals simp_rw [h]; clear h
  rw [deriv_smul_const, deriv_id'', deriv_comp, Polynomial.deriv, deriv_smul_const, deriv_id'']
  simp_rw [one_smul, mul_assoc, ← mul_add]
  have h :
    s * p.sumIDeriv.eval (x • s) -
        (derivative (R := ℂ) (sumIDeriv p)).eval (x • s) * s =
      s * p.eval (x • s) := by
    conv_lhs =>
      congr
      rw [sumIDeriv_eq_self_add, sumIDeriv_derivative]
    rw [mul_comm _ s, eval_add, mul_add, add_sub_cancel_right]
  rw [← mul_neg, neg_add', neg_mul, neg_neg, h, mul_left_comm]
  repeat'
    first
    | fun_prop
    | apply Differentiable.comp
    | apply @Differentiable.restrictScalars ℝ _ ℂ

theorem integral_f_eq (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in (0)..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) -
        -p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul]
  convert
    intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ => -(exp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (deriv_eq_f p s) _ _
  · rw [one_smul]
  · rw [one_smul]
  · simp_rw [zero_smul, neg_zero, Complex.exp_zero, one_mul]
  · intro x _
    apply (Differentiable.mul _ _).neg.differentiableAt
    · apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * s))
      fun_prop
    change Differentiable ℝ ((fun y : ℂ => p.sumIDeriv.eval y) ∘ fun x : ℝ => x • s)
    apply Differentiable.comp
    · apply @Differentiable.restrictScalars ℝ _ ℂ; fun_prop
    · fun_prop
  · fun_prop

def P (p : ℂ[X]) (s : ℂ) :=
  exp s * p.sumIDeriv.eval 0 - p.sumIDeriv.eval s

theorem P_le_aux (p : ℕ → ℂ[X]) (s : ℂ)
    (h :
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q : ℕ,
      Complex.abs (P (p q) s) ≤
        Real.exp s.re * (Real.exp (Complex.abs s) * c ^ q * (Complex.abs s)) := by
  simp_rw [P]; cases' h with c hc; replace hc := fun q x hx => (hc q x hx).trans (le_abs_self _)
  simp_rw [_root_.abs_pow] at hc; use |c|, abs_nonneg _; intro q
  have h := integral_f_eq (p q) s
  rw [← @mul_right_inj' _ _ (exp s) _ _ (exp_ne_zero _),
    neg_sub_neg, mul_sub, ← mul_assoc _ (exp _), ← exp_add, add_neg_cancel, exp_zero, one_mul] at h
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
    (h :
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q ≥ 1, Complex.abs (P (p q) s) ≤ c ^ q := by
  obtain ⟨c', hc', h'⟩ := P_le_aux p s h; clear h
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp (Complex.abs s)) 1
  let c₃ := max (Complex.abs s) 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro q hq; refine (h' q).trans ?_; simp_rw [mul_pow]
  have le_max_one_pow : ∀ {x : ℝ}, x ≤ max x 1 ^ q := fun {x} =>
    (max_cases x 1).elim (fun h => h.1.symm ▸ le_self_pow₀ h.2 (zero_lt_one.trans_le hq).ne')
      fun h => by rw [h.1, one_pow]; exact h.2.le
  gcongr
  all_goals exact le_max_one_pow

open Polynomial

theorem exp_polynomial_approx (p : ℤ[X]) (p0 : p.eval 0 ≠ 0) :
    ∃ c,
      ∀ q > (eval 0 p).natAbs, q.Prime →
        ∃ (n : ℤ) (_ : n % q ≠ 0) (gp : ℤ[X]) (_ : gp.natDegree ≤ q * p.natDegree - 1),
          ∀ {r : ℂ}, r ∈ p.aroots ℂ →
            Complex.abs (n • exp r - q • aeval r gp : ℂ) ≤ c ^ q / (q - 1)! := by
  let p' q := (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ)
  have : ∀ s : ℂ, ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      Complex.abs ((p' q).eval (x • s)) ≤ c ^ q := by
    intro s; dsimp only [p']
    simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
      Complex.abs_pow, real_smul, map_mul, abs_ofReal, ← eval₂_eq_eval_map, ← aeval_def]
    have : Bornology.IsBounded
        ((fun x : ℝ => max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) '' Set.Ioc 0 1) := by
      have h :
        (fun x : ℝ => max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) '' Set.Ioc 0 1 ⊆
          (fun x : ℝ => max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) '' Set.Icc 0 1 :=
        Set.image_subset _ Set.Ioc_subset_Icc_self
      refine (IsCompact.image isCompact_Icc ?_).isBounded.subset h
      fun_prop
    cases' this.exists_norm_le with c h
    use c; intro q x hx
    specialize h (max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) (Set.mem_image_of_mem _ hx)
    refine le_trans ?_ (pow_le_pow_left (norm_nonneg _) h _)
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
    split_ifs with h
    · apply Finset.le_max'; rw [Multiset.mem_toFinset]
      refine Multiset.mem_map_of_mem _ hx
    · rw [Finset.nonempty_iff_ne_empty, Ne, Multiset.toFinset_eq_empty,
        Multiset.eq_zero_iff_forall_not_mem] at h
      push_neg at h
      exact absurd (Multiset.mem_map_of_mem _ hx) (h (c' x))
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
  · rw [Int.add_emod, nsmul_eq_mul, Int.mul_emod_right, add_zero, Int.emod_emod, Ne,
      ← Int.dvd_iff_emod_eq_zero]
    intro h
    replace h := Int.Prime.dvd_pow' prime_q h; rw [Int.natCast_dvd] at h
    replace h := Nat.le_of_dvd (Int.natAbs_pos.mpr p0) h
    revert h; rwa [imp_false, not_le]
  obtain ⟨gp, gp'_le, h⟩ := aeval_sumIDeriv ℂ (X ^ (q - 1) * p ^ q) q
  refine ⟨gp, ?_, ?_⟩
  · refine gp'_le.trans ((tsub_le_tsub_right natDegree_mul_le q).trans ?_)
    rw [natDegree_X_pow, natDegree_pow, tsub_add_eq_add_tsub (Nat.one_le_of_lt q0),
      tsub_right_comm]
    apply tsub_le_tsub_right; rw [add_tsub_cancel_left]
  intro r hr
  have :
    (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ) =
      (X - C r) ^ q *
        (X ^ (q - 1) *
          (C (map (algebraMap ℤ ℂ) p).leadingCoeff *
              (((p.aroots ℂ).erase r).map fun a : ℂ => X - C a).prod) ^
            q) := by
    rw [mul_left_comm, ← mul_pow, mul_left_comm (_ - _),
      Multiset.prod_map_erase (f := fun a => X - C a) hr]
    have : Multiset.card (p.aroots ℂ) = (p.map (algebraMap ℤ ℂ)).natDegree :=
      splits_iff_card_roots.mp (IsAlgClosed.splits _)
    rw [C_leadingCoeff_mul_prod_multiset_X_sub_C this, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, map_X]
  specialize h r this; clear this
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← abs_natCast, ← map_mul,
    mul_comm, mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul, mul_comm,
    Nat.mul_factorial_pred q0, ← h]
  rw [nsmul_eq_mul, ← Int.cast_natCast, ← zsmul_eq_mul, smul_smul, mul_add, ← nsmul_eq_mul, ←
    nsmul_eq_mul, smul_smul, mul_comm, Nat.mul_factorial_pred q0, coe_aeval_eq_eval, ← eval_pow,
    ← h', zsmul_eq_mul, mul_comm, ← eq_intCast (algebraMap ℤ ℂ), eval, hom_eval₂, RingHom.comp_id,
    map_zero, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, ← sumIDeriv_map, ← P]
  exact (Pp'_le r q (Nat.one_le_of_lt q0)).trans (pow_le_pow_left (c'0 r) (hc r hr) _)
