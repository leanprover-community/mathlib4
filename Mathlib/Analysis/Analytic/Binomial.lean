/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.MoveAdd

/-!

# Binomial Series

We introduce the binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
where $a$ is an element of a normed field $\mathbb{K}$,
and $x$ is an element of a normed algebra over $\mathbb{K}$.

## Main Statements

* `binomialSeries_radius_ge_one`: The radius of convergence of the binomial series is at least $1$.
* `binomialSum_eq_rpow`: The series converges to $(1 + x)^a$ for real $a$ and $|x| < 1$.

## Implementation Details

We use `RCLike 𝕂` to leverage the fact that `‖(n : 𝕂)‖ = n` for natural numbers `n`. Without this,
we cannot apply the `descPochhammer_bound_ascPochhammer` bound in our proof.

## TODO

* Generalize `binomialSeries_radius_ge_one` from `RCLike 𝕂` to `NontriviallyNormedField 𝕂`.
* Prove that the radius of convergence of the binomial series is *exactly* $1$.
* Prove the `binomialSum_eq_cpow` variant of `binomialSum_eq_rpow` for complex $a$ and $x$.

-/

open scoped Nat

universe u v

theorem Ring.choose_eq_div {𝕂 : Type v} [Field 𝕂] [CharZero 𝕂]
    {a : 𝕂} {n : ℕ} :
    Ring.choose a n = (n ! : 𝕂)⁻¹ • (descPochhammer ℤ n).smeval a := by
  rw [Ring.descPochhammer_eq_factorial_smul_choose]
  trans (n ! : 𝕂)⁻¹ • ((n ! : 𝕂) • Ring.choose a n)
  · rw [smul_smul]
    rw [inv_mul_cancel₀]
    · simp
    rw [Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero n
  · congr
    apply Nat.cast_smul_eq_nsmul

theorem ascPochhammer_nonneg {R : Type u} [LinearOrderedCommRing R] {a : R} {n : ℕ} (ha : 0 ≤ a) :
    0 ≤ (ascPochhammer ℕ n).smeval a := by
  cases n with
  | zero => simp
  | succ m =>
    simp [ascPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    apply mul_nonneg
    · exact ascPochhammer_nonneg ha
    · linarith

section

variable {𝕂 : Type v} [NormedField 𝕂]

/-- Binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
-/
noncomputable def binomialSeries [CharZero 𝕂] (𝔸 : Type u) [NormedDivisionRing 𝔸] [Algebra 𝕂 𝔸]
    (a : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (Ring.choose a n) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

theorem descPochhammer_bound_ascPochhammer {a : 𝕂} {n : ℕ} :
    ‖(descPochhammer ℤ n).smeval a‖ ≤ (ascPochhammer ℕ n).smeval ‖a‖ := by
  cases n with
  | zero => simp
  | succ m =>
    simp [ascPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast,
      descPochhammer_succ_right]
    apply mul_le_mul
    · exact descPochhammer_bound_ascPochhammer
    · trans ‖a‖ + ‖(m : 𝕂)‖
      · apply norm_sub_le
      simp
      -- the following should be simpler
      conv => lhs; rw [← nsmul_one]
      trans m * ‖(1 : 𝕂)‖
      · apply norm_nsmul_le
      simp
    · simp
    · apply ascPochhammer_nonneg
      simp

end

/-- The radius of convergence of the binomial series is at least 1. -/
theorem binomialSeries_radius_ge_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} : 1 ≤ (binomialSeries 𝔸 a).radius := by
  apply le_of_forall_ge_of_dense
  intro r hr
  cases' r with r <;> simp at hr
  by_cases hr_pos : r = 0
  · simp [hr_pos]
  replace hr_pos : 0 < r := lt_of_le_of_ne (zero_le r) (by solve_by_elim)
  apply FormalMultilinearSeries.le_radius_of_isBigO
  have : ∃ M : ℕ, ‖a‖ * r < M * (1 - r) := by
    conv => arg 1; ext M; rw [← div_lt_iff₀ (by simpa)]
    apply exists_nat_gt
  obtain ⟨M, hM⟩ := this
  have h_bound : ∀ k, (ascPochhammer ℕ (M + k)).smeval ‖a‖ * ((M + k)! : ℝ)⁻¹ * r^k ≤
      (ascPochhammer ℕ M).smeval ‖a‖ * (M ! : ℝ)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ l ih =>
      simp [← add_assoc, Nat.factorial, pow_succ, ascPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_natCast] at ih ⊢
      convert_to (ascPochhammer ℕ (M + l)).smeval ‖a‖ * ((M + l)! : ℝ)⁻¹ * ↑r ^ l *
        (r * (‖a‖ + (↑M + ↑l)) * (M + l + 1 : ℝ)⁻¹) ≤ (ascPochhammer ℕ M).smeval ‖a‖ * (M ! : ℝ)⁻¹
      · ring_nf
      trans
      swap
      · exact ih
      apply mul_le_of_le_one_right
      · apply mul_nonneg
        · apply div_nonneg
          · apply ascPochhammer_nonneg
            simp
          · simp
        · simp
      rw [← div_eq_mul_inv, div_le_one (by linarith)]
      ring_nf at hM ⊢
      have : (r : ℝ) * l ≤ l := by -- for linarith
        apply mul_le_of_le_one_left
        · simp
        · simp
          exact hr.le
      linarith
  apply Asymptotics.IsBigO.of_bound (c := r^M * (ascPochhammer ℕ M).smeval ‖a‖ * ‖(M ! : 𝕂)‖⁻¹)
  simp [binomialSeries]
  use M
  intro b hb
  replace hb := Nat.exists_eq_add_of_le hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  -- for some reason, `rw` below cannot infer it
  have _ : BoundedSMul 𝕂 (ContinuousMultilinearMap 𝕂 (fun (i : Fin (M + k)) ↦ 𝔸) 𝔸) := by
    infer_instance
  rw [norm_smul (Ring.choose a (M + k)) (ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 (M + k) 𝔸)]
  simp [pow_add, div_eq_mul_inv]
  move_mul [r.toReal^M, r.toReal^M]
  apply mul_le_mul_of_nonneg_right _ (by simp)
  simp [Ring.choose_eq_div]
  trans ((M + k) ! : ℝ)⁻¹ * (ascPochhammer ℕ (M + k)).smeval ‖a‖ * ↑r ^ k
  · rw [mul_le_mul_right, mul_le_mul_left]
    · exact descPochhammer_bound_ascPochhammer
    · simp
      apply Nat.factorial_pos
    · apply pow_pos
      simpa
  conv => lhs; arg 1; rw [mul_comm]
  apply h_bound

open ContinuousLinearMap FormalMultilinearSeries

/-- Let `f` denote the binomial series $\sum_{k=0}^{\infty} \binom{a}{k} s^k$.
Then $a \cdot f'(s) = (1 + s) f(s)$, where $f'$ is the formal derivative of the series. -/
theorem binomialSeries_ODE {a : ℝ} :
    let dSeries := (binomialSeries ℝ a).derivSeries
    a • binomialSeries ℝ a = (compFormalMultilinearSeries (.apply ℝ ℝ 1) dSeries) +
      dSeries.unshift 0
    := by
  have h_coeff : ∀ k, (binomialSeries ℝ a).coeff k = (Ring.choose a k) := by
    intro k
    unfold binomialSeries
    simp [coeff]
    -- the following should be simpler
    rw [List.prod_eq_one]
    · simp
    · simp [List.forall_mem_ofFn_iff]
  have h_deriv_coeff : ∀ k, ((binomialSeries ℝ a).derivSeries.coeff k) 1 =
      (Ring.choose a (k + 1)) * (k + 1) := by
    intro k
    simp [derivSeries]
    unfold coeff
    simp [changeOriginSeries, changeOriginSeriesTerm, h_coeff]
    rw [← Finset.sum_mul, mul_comm]
    congr 2
    · ring
    conv => lhs; arg 2; ext; arg 2; ext; arg 2; change fun _ ↦ 1
    have : ∀ x : Fin k ⊕ Fin 1, Sum.elim (1 : Fin k → ℝ) (fun x ↦ 1) x = 1 := by
      intro x
      cases x <;> simp
    conv => lhs; arg 2; ext; arg 2; ext x; rw [this]
    simp [add_comm 1 k]
  simp
  apply FormalMultilinearSeries.ext
  intro n
  simp
  cases n with
  | zero =>
    simp [unshift]
    simp [binomialSeries]
    apply ContinuousMultilinearMap.ext
    intro m
    simp [h_deriv_coeff]
  | succ k =>
    apply ContinuousMultilinearMap.ext
    intro m
    simp only [ContinuousMultilinearMap.smul_apply, apply_eq_prod_smul_coeff, smul_eq_mul, unshift,
      Nat.succ_eq_add_one, ContinuousMultilinearMap.add_apply, compContinuousMultilinearMap_coe,
      Function.comp_apply, map_smul, apply_apply, continuousMultilinearCurryRightEquiv_symm_apply',
      coe_smul', Pi.smul_apply]
    conv => rhs; arg 2; arg 2; arg 2; rw [show m (Fin.last k) = m (Fin.last k) • 1 by simp]
    simp only [map_smul, Algebra.mul_smul_comm]
    simp [smul_eq_mul]
    ring_nf
    rw [show m (Fin.last k) * ∏ i : Fin k, Fin.init m i = ∏ i : Fin (k + 1), m i by
      rw [Fin.prod_univ_castSucc, mul_comm]; rfl]
    trans (∏ i : Fin (k + 1), m i) * (((binomialSeries ℝ a).derivSeries.coeff (1 + k)) 1 +
        ((binomialSeries ℝ a).derivSeries.coeff k) 1)
    swap
    · ring
    move_mul [a]
    rw [mul_assoc, mul_eq_mul_left_iff]
    left
    simp [h_coeff, h_deriv_coeff, Ring.choose_eq_div]
    conv => rhs; arg 1; simp [descPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_natCast]
    rw [add_comm 1 k]
    move_mul [← (descPochhammer ℤ (k + 1)).smeval a]
    conv => lhs; rw [mul_assoc]
    trans (descPochhammer ℤ (k + 1)).smeval a * ((a - (1 + ↑k)) * ((k + 1 + 1)! : ℝ)⁻¹ *
        (1 + ↑k + 1) + ((k + 1)! : ℝ)⁻¹ * (↑k + 1))
    swap
    · ring_nf
    rw [mul_assoc, mul_eq_mul_left_iff]
    left
    rw [Nat.factorial_succ (k + 1)]
    simp [div_eq_mul_inv]
    rw [mul_comm]
    have h : ((k + 1)! : ℝ) ≠ 0 := fun h ↦ Nat.factorial_ne_zero _ (Nat.cast_eq_zero.mp h)
    rw [mul_inv_eq_iff_eq_mul₀ h]
    rw [add_mul]
    move_mul [((k + 1)!⁻¹ : ℝ), ((k + 1)!⁻¹ : ℝ)]
    rw [mul_inv_cancel_right₀ h, mul_inv_cancel_right₀ h]
    rw [show 1 + (k : ℝ) + 1 = k + 1 + 1 by ring]
    rw [inv_mul_cancel_right₀ (by linarith)]
    ring

/-- Sum of the binomial series $\sum_{k=0}^{\infty} \binom{a}{k} s^k$. -/
noncomputable def binomialSum (a : ℝ) (x : ℝ) := (binomialSeries ℝ a).sum x

/-- Let `f` denote the sum of binomial series $\sum_{k=0}^{\infty} \binom{a}{k} s^k$.
Then $a \cdot f'(s) = (1 + s) f(s)$. -/
theorem binomialSum_ODE {a : ℝ} {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (binomialSum a) (a * binomialSum a x / (1 + x)) x := by
  have h_fun : HasFPowerSeriesOnBall (binomialSum a) (binomialSeries ℝ a) 0 1 := by
    apply HasFPowerSeriesOnBall.mono _ (by simp) (binomialSeries_radius_ge_one (𝔸 := ℝ) (a := a))
    apply FormalMultilinearSeries.hasFPowerSeriesOnBall
    apply lt_of_lt_of_le _ binomialSeries_radius_ge_one
    simp
  have h_afun : HasFPowerSeriesOnBall (a • binomialSum a) (a • binomialSeries ℝ a) 0 1 := by
    exact HasFPowerSeriesOnBall.const_smul h_fun
  have h_fderiv := HasFPowerSeriesOnBall.fderiv h_fun
  have h_deriv : HasFPowerSeriesOnBall (deriv (binomialSum a))
    (compFormalMultilinearSeries (.apply ℝ ℝ 1) (binomialSeries ℝ a).derivSeries) 0 1 := by
    convert comp_hasFPowerSeriesOnBall _ h_fderiv
    rfl
  have h_xfderiv : HasFPowerSeriesOnBall (fun x ↦ fderiv ℝ (binomialSum a) x x)
      ((binomialSeries ℝ a).derivSeries.unshift 0) 0 1 := by
    convert HasFPowerSeriesOnBall.unshift h_fderiv using 1
    ext y
    simp
  have h_xderiv : HasFPowerSeriesOnBall (fun x ↦ x * deriv (binomialSum a) x)
      ((binomialSeries ℝ a).derivSeries.unshift 0) 0 1 := by
    convert h_xfderiv using 1
    ext x
    conv => rhs; arg 2; rw [show x = x • 1 by simp]
    simp
  rw [binomialSeries_ODE] at h_afun
  have h_rhs := HasFPowerSeriesOnBall.add h_deriv h_xderiv
  have := HasFPowerSeriesOnBall.unique h_afun h_rhs
  have hx_mem : x ∈ EMetric.ball 0 1 := by
    simp [EMetric.ball]
    rw [← NNReal.coe_lt_coe, coe_nnnorm x]
    rw [Real.norm_eq_abs, NNReal.coe_one]
    rw [abs_lt]
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  specialize this hx_mem
  simp at this
  convert_to a * binomialSum a x = (1 + x) * deriv (binomialSum a) x at this
  · ring
  rw [this, mul_comm, mul_div_cancel_right₀]
  swap
  · linarith [neg_abs_le x]
  apply DifferentiableAt.hasDerivAt
  apply DifferentiableOn.differentiableAt
  pick_goal 2
  · refine IsOpen.mem_nhds ?h.hs.hs hx_mem
    exact EMetric.isOpen_ball
  apply AnalyticOnNhd.differentiableOn
  apply HasFPowerSeriesOnBall.analyticOnNhd
  exact h_fun

/-- The binomial series converges to `(1 + x).rpow a` for real `a` and `|x| < 1`. -/
theorem binomialSum_eq_rpow {a x : ℝ} (hx : |x| < 1) : binomialSum a x = (1 + x)^a := by
  have binomialSum_zero : binomialSum a 0 = 1 := by
    simp [binomialSum, FormalMultilinearSeries.sum]
    rw [tsum_eq_zero_add']
    · simp
      unfold FormalMultilinearSeries.coeff binomialSeries
      simp
    · simp
      exact summable_zero
  by_cases hx_zero : x = 0
  · simp [hx_zero, binomialSum_zero]
  let v : ℝ → ℝ → ℝ := fun t y ↦ a * y / (1 + t)
  let s : ℝ → Set ℝ := fun _ ↦ Set.univ
  suffices h_eqon : Set.EqOn (binomialSum a) (fun y ↦ (1 + y)^a) (Set.Icc (-|x|) |x|) by
    apply h_eqon
    simp
    exact ⟨neg_abs_le x, le_abs_self x⟩
  apply ODE_solution_unique_of_mem_Icc (v := v) (s := s) (t₀ := 0)
    (K := ⟨|a| / (1 - |x|), by apply div_nonneg (by simp); linarith⟩)
  · intro t ht
    simp at ht
    simp [s, v]
    apply LipschitzWith.weaken (K := ⟨|a| / (1 + t), by apply div_nonneg (by simp); linarith⟩)
    conv => arg 2; ext x; rw [mul_comm, ← mul_div, mul_comm]; change (a / (1 + t)) • x
    convert lipschitzWith_smul _ <;> try infer_instance
    · simp [nnnorm]
      rw [Subtype.eq_iff]
      simp
      rw [abs_of_nonneg (a := 1 + t)]
      linarith
    · rw [← NNReal.coe_le_coe]
      simp
      exact div_le_div_of_nonneg_left (by simp) (by linarith) (by linarith)
  · simpa
  · apply ContinuousOn.mono (s := EMetric.ball 0 (binomialSeries ℝ a).radius)
    · unfold binomialSum
      convert FormalMultilinearSeries.continuousOn
      infer_instance
    · intro x hx
      simp at hx
      simp [EMetric.ball]
      apply lt_of_lt_of_le _ binomialSeries_radius_ge_one
      rw [← ENNReal.coe_one, ENNReal.coe_one, ENNReal.coe_lt_one_iff]
      rw [← NNReal.coe_lt_coe, coe_nnnorm x]
      rw [Real.norm_eq_abs, NNReal.coe_one]
      rw [abs_lt]
      constructor <;> linarith
  · intro t ht
    simp [v]
    apply binomialSum_ODE
    simp at ht
    rw [abs_lt]
    constructor <;> linarith
  · simp [s]
  · apply ContinuousOn.rpow_const
    · apply ContinuousOn.add
      · exact continuousOn_const
      · apply continuousOn_id
    · intro x hx
      left
      simp at hx
      linarith
  · intro t ht
    simp at ht
    simp [v]
    conv => arg 2; rw [← mul_div, ← Real.rpow_sub_one (by linarith)]
    have := HasDerivAt.rpow_const (f := fun x ↦ 1 + x) (p := a) (x := t) (f' := 1)
    simp only [one_mul] at this
    apply this
    · apply HasDerivAt.const_add
      apply hasDerivAt_id
    · left
      linarith
  · simp [s]
  · simpa
