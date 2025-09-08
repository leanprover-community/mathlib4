/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic.MoveAdd
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.RingTheory.Binomial
/-!
# TODO: upstream
-/

namespace TendstoTactic

namespace ForPow

open scoped Nat

universe u v w

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
    simp only [ascPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.ascPochhammer_smeval_cast, Polynomial.smeval_add, Polynomial.smeval_X, pow_one,
      Polynomial.smeval_natCast, pow_zero, nsmul_eq_mul, mul_one]
    apply mul_nonneg
    · exact ascPochhammer_nonneg ha
    · linarith

section

variable {𝕂 : Type v} [NormedField 𝕂]
variable (𝔸 : Type u) [NormedDivisionRing 𝔸] [Algebra 𝕂 𝔸]

/-- **Binomial series**: the (scalar) formal multilinear series with coefficients given
by `Ring.choose a`. The sum of this series is `fun x ↦ (1 + x) ^ a` within the radius
of convergence. -/
noncomputable def binomialSeries [CharZero 𝕂] (a : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (Ring.choose a n) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

theorem descPochhammer_bound_ascPochhammer {a : 𝕂} {n : ℕ} :
    ‖(descPochhammer ℤ n).smeval a‖ ≤ (ascPochhammer ℕ n).smeval ‖a‖ := by
  cases n with
  | zero => simp
  | succ m =>
    simp only [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, pow_one, Polynomial.smeval_natCast, pow_zero, nsmul_eq_mul, mul_one,
      norm_mul, ascPochhammer_succ_right, Polynomial.ascPochhammer_smeval_cast,
      Polynomial.smeval_add]
    apply mul_le_mul
    · exact descPochhammer_bound_ascPochhammer
    · trans ‖a‖ + ‖(m : 𝕂)‖
      · apply norm_sub_le
      simp only [add_le_add_iff_left]
      -- the following should be simpler
      conv_lhs => rw [← nsmul_one]
      trans m * ‖(1 : 𝕂)‖
      · apply norm_nsmul_le
      simp
    · simp
    · apply ascPochhammer_nonneg
      simp

end

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
  have : ∀ k, (ascPochhammer ℕ (M + k)).smeval ‖a‖ * ((M + k)! : ℝ)⁻¹ * r^k ≤
      (ascPochhammer ℕ M).smeval ‖a‖ * (M ! : ℝ)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ l ih =>
      simp only [Polynomial.ascPochhammer_smeval_cast, ← add_assoc, ascPochhammer_succ_right,
        Nat.cast_add, Polynomial.smeval_mul, Polynomial.smeval_add, Polynomial.smeval_X, pow_succ,
        pow_zero, one_mul, Polynomial.smeval_natCast, nsmul_eq_mul, mul_one, Nat.factorial,
        Nat.add_eq, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_one, mul_inv_rev] at ih ⊢
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
        · simp only [NNReal.coe_le_one]
          exact hr.le
      linarith
  apply Asymptotics.IsBigO.of_bound (c := r^M * (ascPochhammer ℕ M).smeval ‖a‖ * ‖(M ! : 𝕂)‖⁻¹)
  simp [binomialSeries]
  use M
  intro b hb
  replace hb := Nat.exists_eq_add_of_le hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  trans ‖Ring.choose a (M + k)‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 (M + k) 𝔸‖ *
    r ^ (M + k)
  · rw [mul_le_mul_right]
    · apply ContinuousMultilinearMap.opNorm_smul_le
    · apply pow_pos
      simpa
  simp only [ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one, pow_add]
  move_mul [r.toReal^M, r.toReal^M]
  apply mul_le_mul_of_nonneg_right _ (by simp)
  simp only [Ring.choose_eq_div, smul_eq_mul, norm_mul, norm_inv, RCLike.norm_natCast]
  trans ((M + k) ! : ℝ)⁻¹ * (ascPochhammer ℕ (M + k)).smeval ‖a‖ * ↑r ^ k
  · rw [mul_le_mul_right, mul_le_mul_left]
    · exact descPochhammer_bound_ascPochhammer
    · simp only [inv_pos, Nat.cast_pos]
      apply Nat.factorial_pos
    · apply pow_pos
      simpa
  conv_lhs => arg 1; rw [mul_comm]
  apply this

open ContinuousLinearMap FormalMultilinearSeries

theorem binomialSeries_ODE {a : ℝ} :
    let dSeries := (binomialSeries ℝ a).derivSeries
    a • binomialSeries ℝ a = (compFormalMultilinearSeries (.apply ℝ ℝ 1) dSeries) +
      dSeries.unshift 0 := by
  have h_coeff : ∀ k, (binomialSeries ℝ a).coeff k = (Ring.choose a k) := by
    intro k
    unfold binomialSeries
    simp only [coeff, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul]
    rw [List.prod_eq_one] -- cringe
    · simp
    · simp [List.forall_mem_ofFn_iff]
  have h_deriv_coeff : ∀ k, ((binomialSeries ℝ a).derivSeries.coeff k) 1 =
      (Ring.choose a (k + 1)) * (k + 1) := by
    intro k
    simp only [derivSeries]
    unfold coeff
    simp only [compFormalMultilinearSeries_apply, changeOriginSeries, changeOriginSeriesTerm,
      compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
      Function.comp_apply, ContinuousMultilinearMap.sum_apply, map_sum, coe_sum', Finset.sum_apply,
      continuousMultilinearCurryFin1_apply, Matrix.zero_empty,
      ContinuousMultilinearMap.curryFinFinset_apply, apply_eq_prod_smul_coeff, h_coeff, smul_eq_mul]
    rw [← Finset.sum_mul, mul_comm]
    congr 2
    · ring
    conv_lhs => arg 2; ext; arg 2; ext; arg 2; change fun _ ↦ 1
    have : ∀ x : Fin k ⊕ Fin 1, Sum.elim (1 : Fin k → ℝ) (fun x ↦ 1) x = 1 := by
      intro x
      cases x <;> simp
    conv_lhs => arg 2; ext; arg 2; ext x; rw [this]
    simp [add_comm 1 k]
  simp only
  apply FormalMultilinearSeries.ext
  intro n
  simp only [FormalMultilinearSeries.smul_apply, FormalMultilinearSeries.add_apply,
    compFormalMultilinearSeries_apply]
  cases n with
  | zero =>
    simp only [unshift, map_zero, add_zero]
    simp only [binomialSeries, Ring.choose_zero_right', pow_zero, one_smul]
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
    conv_rhs => arg 2; arg 2; arg 2; rw [show m (Fin.last k) = m (Fin.last k) • 1 by simp]
    simp only [map_smul, Algebra.mul_smul_comm]
    simp only [smul_eq_mul]
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
    simp only [h_coeff, Ring.choose_eq_div, smul_eq_mul, h_deriv_coeff, Nat.cast_add, Nat.cast_one]
    conv_rhs => arg 1; simp [descPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_natCast]
    rw [add_comm 1 k]
    move_mul [← (descPochhammer ℤ (k + 1)).smeval a]
    conv_lhs => rw [mul_assoc]
    trans (descPochhammer ℤ (k + 1)).smeval a * ((a - (1 + ↑k)) * ((k + 1 + 1)! : ℝ)⁻¹ *
      (1 + ↑k + 1) + ((k + 1)! : ℝ)⁻¹ * (↑k + 1))
    swap
    · ring_nf
    rw [mul_assoc, mul_eq_mul_left_iff]
    left
    rw [Nat.factorial_succ (k + 1)]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
    rw [mul_comm]
    have h : ((k + 1)! : ℝ) ≠ 0 := fun h ↦ Nat.factorial_ne_zero _ (Nat.cast_eq_zero.mp h)
    rw [mul_inv_eq_iff_eq_mul₀ h]
    rw [add_mul]
    move_mul [((k + 1)!⁻¹ : ℝ), ((k + 1)!⁻¹ : ℝ)]
    rw [mul_inv_cancel_right₀ h, mul_inv_cancel_right₀ h]
    rw [show 1 + (k : ℝ) + 1 = k + 1 + 1 by ring]
    rw [inv_mul_cancel_right₀ (by linarith)]
    ring

/-- Sum of the binomial series. -/
noncomputable def binomialSum (a : ℝ) (x : ℝ) := (binomialSeries ℝ a).sum x

-- TODO: move
theorem HasFPowerSeriesOnBall.unique {𝕜 : Type u} {E : Type v} {F : Type w}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f g : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ENNReal}
    (hf : HasFPowerSeriesOnBall f p x r)
    (hg : HasFPowerSeriesOnBall g p x r) :
    Set.EqOn f g (EMetric.ball x r) := by
  intro y hy
  have hf_sum := hf.hasSum_sub hy
  have hg_sum := hg.hasSum_sub hy
  apply HasSum.unique hf_sum hg_sum

-- TODO: move
theorem HasFPowerSeriesOnBall.smul {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    {F : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {c : 𝕜} {pf : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (c • f) (c • pf) x r := by
  constructor
  · simp only [radius, FormalMultilinearSeries.smul_apply]
    trans
    · exact h.r_le
    simp only [radius]
    apply iSup_mono
    intro r
    apply iSup_mono'
    intro C
    use ‖c‖ * C
    apply iSup_mono'
    intro h
    simp only [le_refl, exists_prop, and_true]
    intro n
    trans ‖c‖ * ‖pf n‖ * (r : NNReal) ^ n
    · apply mul_le_mul_of_nonneg_right
      · apply ContinuousMultilinearMap.opNorm_smul_le
      · apply pow_nonneg
        simp
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left
    · apply h
    · simp
  · exact h.r_pos
  · intro y hy
    apply HasSum.const_smul
    exact h.hasSum hy

-- TODO: move
theorem HasFPowerSeriesOnBall.unshift {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)} {r : ENNReal} {f : E → (E →L[𝕜] F)} {x : E}
    (h : HasFPowerSeriesOnBall f p x r) {z : F} :
    HasFPowerSeriesOnBall (fun y ↦ z + f y (y - x)) (p.unshift z) x r := by
  constructor
  · simp only [radius]
    trans
    · exact h.r_le
    simp only [radius]
    apply iSup_mono
    intro r
    apply iSup_mono'
    intro C
    use C * r + ‖z‖
    apply iSup_mono'
    intro h
    simp only [le_refl, exists_prop, and_true]
    intro n
    have hC : 0 ≤ C := by
      specialize h 0
      simp only [pow_zero, mul_one] at h
      trans ‖p 0‖
      · apply ContinuousMultilinearMap.opNorm_nonneg
      · exact h
    cases' n with k
    · simp only [FormalMultilinearSeries.unshift, LinearIsometryEquiv.norm_map, pow_zero, mul_one,
      le_add_iff_nonneg_left, ge_iff_le]
      apply mul_nonneg hC
      simp
    · simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      LinearIsometryEquiv.norm_map, pow_succ, ge_iff_le]
      trans C * r
      · rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by simp)
        apply h
      · simp
  · exact h.r_pos
  · intro y hy
    apply HasSum.zero_add
    simp_rw [FormalMultilinearSeries.unshift.eq_2]
    simp only [Nat.succ_eq_add_one, continuousMultilinearCurryRightEquiv_symm_apply',
      add_sub_cancel_left]
    conv => arg 1; ext n; arg 1; arg 2; change fun _ ↦ y
    have := ContinuousLinearMap.hasSum (ContinuousLinearMap.apply 𝕜 F y) (h.hasSum hy)
    simpa using this

theorem binomialSum_ODE {a : ℝ} {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (binomialSum a) (a * binomialSum a x / (1 + x)) x := by
  have h_fun : HasFPowerSeriesOnBall (binomialSum a) (binomialSeries ℝ a) 0 1 := by
    apply HasFPowerSeriesOnBall.mono _ (by simp) (binomialSeries_radius_ge_one (𝔸 := ℝ) (a := a))
    apply FormalMultilinearSeries.hasFPowerSeriesOnBall
    apply lt_of_lt_of_le _ binomialSeries_radius_ge_one
    simp
  have h_afun : HasFPowerSeriesOnBall (a • binomialSum a) (a • binomialSeries ℝ a) 0 1 := by
    exact HasFPowerSeriesOnBall.smul h_fun
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
    conv_rhs => arg 2; rw [show x = x • 1 by simp]
    simp
  rw [binomialSeries_ODE] at h_afun
  have h_rhs := HasFPowerSeriesOnBall.add h_deriv h_xderiv
  have := HasFPowerSeriesOnBall.unique h_afun h_rhs
  have hx_mem : x ∈ EMetric.ball 0 1 := by
    simp only [EMetric.ball, edist_zero_right, ENNReal.coe_lt_one_iff, Set.mem_setOf_eq]
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

-- TODO: move
/-- TODO -/
theorem ODE_solution_unique_of_mem_Icc' {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f g : ℝ → E} {a b t₀ : ℝ}
    (hv : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K (v t) (s t)) (ht : t₀ ∈ Set.Ioo a b)
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ∀ t ∈ Set.Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ Set.Ioo a b, f t ∈ s t) (hg : ContinuousOn g (Set.Icc a b))
    (hg' : ∀ t ∈ Set.Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ Set.Ioo a b, g t ∈ s t) (heq : f t₀ = g t₀) :
    Set.EqOn f g (Set.Icc a b) := by
  let v' : ℝ → E → E := fun t x ↦ if t ∈ Set.Ioo a b then v t x else 0
  apply ODE_solution_unique_of_mem_Icc (v := v') (s := s) (t₀ := t₀) (K := K)
  all_goals try assumption
  · intro t
    by_cases h : t ∈ Set.Ioo a b
    · simp only [v', h]
      simp only [↓reduceIte]
      apply hv _ h
    · simp only [v', h]
      simp only [↓reduceIte]
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.const'
  · intro t ht
    simp only [v', ht]
    simp only [↓reduceIte]
    apply hf' _ ht
  · intro t ht
    simp only [v', ht]
    simp only [↓reduceIte]
    apply hg' _ ht

theorem binomialSum_eq_rpow_aux {a : ℝ} {ε : ℝ} (hε : 0 < ε) :
    Set.EqOn (binomialSum a) (fun x ↦ (1 + x)^a) (Set.Icc (-1 + ε) (1 - ε)) := by
  have binomialSum_zero : binomialSum a 0 = 1 := by
    simp only [binomialSum, FormalMultilinearSeries.sum, apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [tsum_eq_zero_add']
    · simp only [pow_zero, one_mul, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, tsum_zero, add_zero]
      unfold FormalMultilinearSeries.coeff binomialSeries
      simp
    · simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, zero_mul]
      exact summable_zero
  rcases lt_trichotomy ε 1 with (hε' | hε' | hε')
  rotate_left
  · simp [hε', binomialSum_zero]
  · convert Set.eqOn_empty _ _
    apply Set.Icc_eq_empty
    linarith
  let v : ℝ → ℝ → ℝ := fun t x ↦ a * x / (1 + t)
  let s : ℝ → Set ℝ := fun _ ↦ Set.univ
  apply ODE_solution_unique_of_mem_Icc' (v := v) (s := s) (t₀ := 0)
    (K := ⟨|a| / ε, by apply div_nonneg (by simp); linarith⟩)
  · intro t ht
    simp only [Set.mem_Ioo, neg_add_lt_iff_lt_add] at ht
    simp only [lipschitzOnWith_univ, v, s]
    apply LipschitzWith.weaken (K := ⟨|a| / (1 + t), by apply div_nonneg (by simp); linarith⟩)
    conv => arg 2; ext x; rw [mul_comm, ← mul_div, mul_comm]; change (a / (1 + t)) • x
    convert lipschitzWith_smul _ <;> try infer_instance
    · simp only [nnnorm, norm_div, Real.norm_eq_abs]
      rw [Subtype.eq_iff]
      simp only
      rw [abs_of_nonneg (a := 1 + t)]
      linarith
    · rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_mk]
      exact div_le_div_of_nonneg_left (by simp) hε (by linarith)
  · simpa
  · apply ContinuousOn.mono (s := EMetric.ball 0 (binomialSeries ℝ a).radius)
    · unfold binomialSum
      convert FormalMultilinearSeries.continuousOn
      infer_instance -- why asked?
    · intro x hx
      simp only [Set.mem_Icc, neg_add_le_iff_le_add] at hx
      simp only [EMetric.ball, edist_zero_right, Set.mem_setOf_eq]
      apply lt_of_lt_of_le _ binomialSeries_radius_ge_one
      rw [← ENNReal.coe_one, ENNReal.coe_one, ENNReal.coe_lt_one_iff]
      rw [← NNReal.coe_lt_coe, coe_nnnorm x]
      rw [Real.norm_eq_abs, NNReal.coe_one]
      rw [abs_lt]
      constructor <;> linarith
  · intro t ht
    simp only [v]
    apply binomialSum_ODE
    simp only [Set.mem_Ioo, neg_add_lt_iff_lt_add] at ht
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
    simp only [Set.mem_Ioo, neg_add_lt_iff_lt_add] at ht
    simp only [v]
    conv => arg 2; rw [← mul_div, ← Real.rpow_sub_one (by linarith)]
    have := HasDerivAt.rpow_const (f := fun x ↦ 1 + x) (p := a) (x := t) (f' := 1)
    simp only [one_mul] at this
    apply this
    · apply HasDerivAt.const_add
      apply hasDerivAt_id
    · left
      linarith
  · simp [s]
  · simp [binomialSum_zero]

theorem binomialSum_eq_rpow {a x : ℝ} (hx : |x| < 1) : binomialSum a x = (1 + x)^a := by
  let ε := (1 - |x|) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have := binomialSum_eq_rpow_aux (a := a) hε
  apply this
  simp only [Set.mem_Icc, neg_add_le_iff_le_add]
  rw [abs_lt] at hx
  dsimp [ε]
  constructor <;> linarith [le_abs_self x, neg_abs_le x]

end ForPow

end TendstoTactic
