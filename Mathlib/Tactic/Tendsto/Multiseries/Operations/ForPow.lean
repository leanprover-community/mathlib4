import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic.MoveAdd
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.Linarith.Oracle.FourierMotzkin

set_option linter.style.longLine false

namespace TendstoTactic

namespace ForPow

theorem ascPochhammer_nonneg {a : ℝ} {n : ℕ} (ha : 0 ≤ a) : 0 ≤ (ascPochhammer ℕ n).smeval a := by
  cases n with
  | zero => simp
  | succ m =>
    simp [ascPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    apply mul_nonneg
    · exact ascPochhammer_nonneg ha
    · linarith

theorem descPochhammer_bound_ascPochhammer {a : ℝ} {n : ℕ} :
    |(descPochhammer ℤ n).smeval a| ≤ (ascPochhammer ℕ n).smeval |a| := by
  cases n with
  | zero => simp
  | succ m =>
    simp [ascPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast,
      descPochhammer_succ_right, abs_mul]
    apply mul_le_mul
    · exact descPochhammer_bound_ascPochhammer
    · convert abs_sub a (↑m)
      simp
    · simp
    · apply ascPochhammer_nonneg
      simp

open Filter Asymptotics

open scoped Nat

universe u v w

-- variable (𝔸 : Type*) [Ring 𝔸] [Algebra ℝ 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

noncomputable def binomialCoef (a : ℝ) (n : ℕ) : ℝ := Ring.choose a n

@[simp]
theorem binomialCoef_zero {a : ℝ} : binomialCoef a 0 = 1 := by
  simp [binomialCoef]

@[simp]
theorem binomialCoef_one {a : ℝ} : binomialCoef a 1 = a := by
  simp [binomialCoef]

noncomputable def binomialSeries (a : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ := fun n =>
  (binomialCoef a n) • ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ

-- variable [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸] [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]

lemma Ring.choose_eq_div {a : ℝ} {n : ℕ} :
    Ring.choose a n = (descPochhammer ℤ n).smeval a / n.factorial := by
  apply eq_div_of_mul_eq (by simp [Nat.factorial_ne_zero])
  convert_to n ! • Ring.choose a n = (descPochhammer ℤ n).smeval a
  · ring
  rw [Ring.descPochhammer_eq_factorial_smul_choose]

theorem binomialSeries_radius_ge_one {a : ℝ} : 1 ≤ (binomialSeries a).radius := by
  apply le_of_forall_ge_of_dense
  intro r hr
  cases' r with r <;> simp at hr
  by_cases hr_pos : r = 0
  · simp [hr_pos]
  replace hr_pos : 0 < r := lt_of_le_of_ne (zero_le r) (by solve_by_elim)
  apply FormalMultilinearSeries.le_radius_of_isBigO
  have : ∃ M : ℕ, |a| * r < M * (1 - r) := by
    conv => arg 1; ext M; rw [← div_lt_iff₀ (by simpa)]
    apply exists_nat_gt
  obtain ⟨M, hM⟩ := this
  have : ∀ k, (ascPochhammer ℕ (M + k)).smeval |a| / (M + k).factorial * r^k ≤
      (ascPochhammer ℕ M).smeval |a| / M.factorial := by
    intro k
    induction k with
    | zero => simp
    | succ l ih =>
      simp [← add_assoc, Nat.factorial, pow_succ, ascPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_natCast] at ih ⊢
      convert_to (ascPochhammer ℕ (M + l)).smeval |a| / ↑(M + l)! * ↑r ^ l * (r * (|a| + (↑M + ↑l)) / (↑M + ↑l + 1)) ≤ (ascPochhammer ℕ M).smeval |a| / ↑M !
      · simp only [div_eq_mul_inv, mul_inv_rev]
        ring_nf
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
      rw [div_le_one (by linarith)]
      ring_nf at hM ⊢
      have : (r : ℝ) * l ≤ l := by -- for linarith
        apply mul_le_of_le_one_left
        · simp
        · simp
          exact hr.le
      linarith
  apply Asymptotics.IsBigO.of_bound (c := r^M * (ascPochhammer ℕ M).smeval |a| / ↑M.factorial)
  simp [binomialSeries]
  use M
  intro b hb
  replace hb := Nat.exists_eq_add_of_le hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  trans ‖binomialCoef a (M + k)‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ (M + k) ℝ‖ * ↑r ^ (M + k)
  · rw [mul_le_mul_right]
    · apply ContinuousMultilinearMap.opNorm_smul_le
    · apply pow_pos
      simpa
  simp [pow_add, div_eq_mul_inv]
  move_mul [r.toReal^M, r.toReal^M]
  apply mul_le_mul_of_nonneg_right _ (by simp)
  simp [binomialCoef, Ring.choose_eq_div, abs_div]
  trans (ascPochhammer ℕ (M + k)).smeval |a| * (↑(M + k)!)⁻¹ * ↑r ^ k
  · simp only [div_eq_mul_inv]
    rw [mul_le_mul_right, mul_le_mul_right]
    · exact descPochhammer_bound_ascPochhammer
    · simp
      linarith [Nat.factorial_pos (M + k)]
    · apply pow_pos
      simpa
  simp only [div_eq_mul_inv] at this ⊢
  apply this

open ContinuousLinearMap FormalMultilinearSeries

theorem binomialSeries_ODE {a : ℝ} :
    let dSeries := (binomialSeries a).derivSeries
    a • binomialSeries a = (compFormalMultilinearSeries (ContinuousLinearMap.apply ℝ ℝ 1) dSeries) +
      dSeries.unshift 0
    := by
  have h_coeff : ∀ k, (binomialSeries a).coeff k = (binomialCoef a k) := by
    intro k
    unfold binomialSeries
    simp [coeff]
    rw [List.prod_eq_one] -- cringe
    · simp
    · simp [List.forall_mem_ofFn_iff]
  have h_deriv_coeff : ∀ k, ((binomialSeries a).derivSeries.coeff k) 1 = (binomialCoef a (k + 1)) * (k + 1) := by
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
    simp [FormalMultilinearSeries.unshift]
    simp [binomialSeries, binomialCoef]
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
    rw [show m (Fin.last k) * ∏ i : Fin k, Fin.init m i = ∏ i : Fin (k + 1), m i by rw [Fin.prod_univ_castSucc, mul_comm]; rfl]
    trans (∏ i : Fin (k + 1), m i) * (((binomialSeries a).derivSeries.coeff (1 + k)) 1 +
        ((binomialSeries a).derivSeries.coeff k) 1)
    swap
    · ring
    move_mul [a]
    rw [mul_assoc, mul_eq_mul_left_iff]
    left
    simp [h_coeff, h_deriv_coeff]
    simp [binomialCoef, Ring.choose_eq_div]
    conv => rhs; arg 1; simp [descPochhammer_succ_right,  Polynomial.smeval_mul,
      Polynomial.smeval_natCast]
    rw [add_comm 1 k]
    trans (descPochhammer ℤ (k + 1)).smeval a * ((a - (1 + ↑k)) / ↑(k + 1 + 1)! * (1 + ↑k + 1) +
        1 / ↑(k + 1)! * (↑k + 1))
    swap
    · ring_nf
    rw [div_eq_mul_inv, mul_assoc, mul_eq_mul_left_iff]
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

noncomputable def binomialSum (a : ℝ) (x : ℝ) := (binomialSeries a).sum x

-- TODO: move
theorem HasFPowerSeriesOnBall.unique {𝕜 : Type u} {E : Type v} {F : Type w} [NontriviallyNormedField 𝕜]
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
    simp
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
    {p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)} {r : ENNReal} {f : E → (E →L[𝕜] F)} {x : E} [CompleteSpace F]
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
    simp
    intro n
    have hC : 0 ≤ C := by
      specialize h 0
      simp at h
      trans ‖p 0‖
      · apply ContinuousMultilinearMap.opNorm_nonneg
      · exact h
    cases' n with k
    · simp [FormalMultilinearSeries.unshift]
      apply mul_nonneg hC
      simp
    · simp [FormalMultilinearSeries.unshift, pow_succ]
      trans C * r
      · rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by simp)
        apply h
      · simp
  · exact h.r_pos
  · intro y hy
    apply HasSum.zero_add
    simp_rw [FormalMultilinearSeries.unshift.eq_2]
    simp
    conv => arg 1; ext n; arg 1; arg 2; change fun _ ↦ y
    have := ContinuousLinearMap.hasSum (ContinuousLinearMap.apply 𝕜 F y) (h.hasSum hy)
    simpa using this

theorem binomialSum_ODE {a : ℝ} {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (binomialSum a) (a * binomialSum a x / (1 + x)) x := by
  have h_fun : HasFPowerSeriesOnBall (binomialSum a) (binomialSeries a) 0 1 := by
    apply HasFPowerSeriesOnBall.mono _ (by simp) (@binomialSeries_radius_ge_one a)
    apply FormalMultilinearSeries.hasFPowerSeriesOnBall
    apply lt_of_lt_of_le _ binomialSeries_radius_ge_one
    simp
  have h_afun : HasFPowerSeriesOnBall (a • binomialSum a) (a • binomialSeries a) 0 1 := by
    exact HasFPowerSeriesOnBall.smul h_fun
  have h_fderiv := HasFPowerSeriesOnBall.fderiv h_fun
  have h_deriv : HasFPowerSeriesOnBall (deriv (binomialSum a))
    (compFormalMultilinearSeries (ContinuousLinearMap.apply ℝ ℝ 1) (binomialSeries a).derivSeries) 0 1 := by
    convert ContinuousLinearMap.comp_hasFPowerSeriesOnBall _ h_fderiv
    rfl
  have h_xfderiv : HasFPowerSeriesOnBall (fun x ↦ fderiv ℝ (binomialSum a) x x) ((binomialSeries a).derivSeries.unshift 0) 0 1 := by
    convert HasFPowerSeriesOnBall.unshift h_fderiv using 1
    ext y
    simp
  have h_xderiv : HasFPowerSeriesOnBall (fun x ↦ x * deriv (binomialSum a) x) ((binomialSeries a).derivSeries.unshift 0) 0 1 := by
    convert h_xfderiv using 1
    ext x
    conv => rhs; arg 2; rw [show x = x • 1 by simp]
    simp
  rw [binomialSeries_ODE] at h_afun
  have h_rhs := HasFPowerSeriesOnBall.add h_deriv h_xderiv
  have := HasFPowerSeriesOnBall.unique h_afun h_rhs
  have hx_mem : x ∈ EMetric.ball 0 1 := by
    simp [EMetric.ball]
    have := coe_nnnorm x
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
      simp
      apply hv _ h
    · simp only [v', h]
      simp
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.const'
  · intro t ht
    simp only [v', ht]
    simp
    apply hf' _ ht
  · intro t ht
    simp only [v', ht]
    simp
    apply hg' _ ht

theorem binomialSum_eq_rpow_aux {a : ℝ} {ε : ℝ} (hε : 0 < ε) : Set.EqOn (binomialSum a) (fun x ↦ (1 + x)^a) (Set.Icc (-1 + ε) (1 - ε)) := by
  have binomialSum_zero : binomialSum a 0 = 1 := by
    simp [binomialSum, FormalMultilinearSeries.sum]
    rw [tsum_eq_zero_add']
    · simp
      unfold FormalMultilinearSeries.coeff binomialSeries
      simp [binomialCoef]
    · simp
      exact summable_zero
  rcases lt_trichotomy ε 1 with (hε' | hε' | hε')
  rotate_left
  · simp [hε', binomialSum_zero]
  · convert Set.eqOn_empty _ _
    apply Set.Icc_eq_empty
    linarith
  have h_sum_analytic : AnalyticOnNhd ℝ (binomialSum a) (EMetric.ball 0 1) := by
    apply AnalyticOnNhd.mono _ (EMetric.ball_subset_ball (@binomialSeries_radius_ge_one a))
    unfold binomialSum
    apply HasFPowerSeriesOnBall.analyticOnNhd (p := binomialSeries a)
    apply FormalMultilinearSeries.hasFPowerSeriesOnBall
    apply lt_of_lt_of_le _ binomialSeries_radius_ge_one
    simp
  let v : ℝ → ℝ → ℝ := fun t x ↦ a * x / (1 + t)
  let s : ℝ → Set ℝ := fun _ ↦ Set.univ
  apply ODE_solution_unique_of_mem_Icc' (v := v) (s := s) (t₀ := 0)
    (K := ⟨|a| / ε, by apply div_nonneg (by simp); linarith⟩)
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
      exact div_le_div_of_nonneg_left (by simp) hε (by linarith)
  · simpa
  · apply ContinuousOn.mono (s := EMetric.ball 0 (binomialSeries a).radius)
    · unfold binomialSum
      convert FormalMultilinearSeries.continuousOn
      infer_instance -- why asked?
    · intro x hx
      simp at hx
      simp [EMetric.ball]
      have := coe_nnnorm x
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
  · simp [binomialSum_zero]

theorem binomialSum_eq_rpow {a x : ℝ} (hx : |x| < 1) : binomialSum a x = (1 + x)^a := by
  let ε := (1 - |x|) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have := binomialSum_eq_rpow_aux (a := a) hε
  apply this
  simp
  rw [abs_lt] at hx
  dsimp [ε]
  constructor <;> linarith [le_abs_self x, neg_abs_le x]

end ForPow

end TendstoTactic
