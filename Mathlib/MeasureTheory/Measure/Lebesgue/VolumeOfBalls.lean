/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Volume of balls

Let `E` be a finite dimensional normed `ℝ`-vector space equipped with an Haar measure `μ`. Then, we
prove that
`μ (Metric.ball 0 1) = (∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)`
for any real number `p` with `0 < p`, see `MeasureTheorymeasure_unitBall_eq_integral_div_gamma`. We
also prove the corresponding result to compute `μ {x : E | g x < 1}` where `g : E → ℝ` is a function
defining a norm on `E`, see `MeasureTheory.measure_lt_one_eq_integral_div_gamma`.

Using these formula, we compute the volume of the unit balls for the norms `L_p` for `1 ≤ p` in any
dimension over the reals `volume_sum_rpow_lt_one` and the complex `Complex.volume_sum_rpow_lt_one`.
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- See issue lean4#2220

section integrals

open Real Set MeasureTheory MeasureTheory.Measure

theorem integral_rpow_mul_exp_neg_rpow {p q : ℝ} (hp : 0 < p) (hq : - 1 < q) :
    ∫ x in Ioi (0:ℝ), x ^ q * exp (- x ^ p) = (1 / p) * Gamma ((q + 1) / p) := by
  calc
    _ = ∫ (x : ℝ) in Ioi 0,  (1 / p * x ^ (1 / p - 1)) • ((x ^ (1 / p)) ^ q * exp (-x)) := by
      rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp)),
        abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp))]
      refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx) _ p, one_div_mul_cancel (ne_of_gt hp), rpow_one]
    _ = ∫ (x : ℝ) in Ioi 0, 1 / p * exp (-x) * x ^ (1 / p - 1 + q / p) := by
      simp_rw [smul_eq_mul, mul_assoc]
      refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx), div_mul_eq_mul_div, one_mul, rpow_add hx]
      ring_nf
    _ = (1 / p) * Gamma ((q + 1) / p) := by
      rw [Gamma_eq_integral (div_pos (neg_lt_iff_pos_add.mp hq) hp)]
      simp_rw [show 1 / p - 1 + q / p = (q + 1) / p - 1 by field_simp; ring, ← integral_mul_left,
        ← mul_assoc]

theorem integral_rpow_mul_exp_neg_mul_rpow {p q b : ℝ} (hp : 0 < p) (hq : - 1 < q) (hb : 0 < b) :
    ∫ x in Ioi (0:ℝ), x ^ q * exp (- b * x ^ p) =
      b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
  calc
    _ = ∫ x in Ioi (0:ℝ), b ^ (-p⁻¹ * q) * ((b ^ p⁻¹ * x) ^ q * rexp (-(b ^ p⁻¹ * x) ^ p)) := by
      refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
      rw [mul_rpow _ (le_of_lt hx), mul_rpow _ (le_of_lt hx), ← rpow_mul, ← rpow_mul,
        inv_mul_cancel, rpow_one, mul_assoc, ← mul_assoc, ← rpow_add, neg_mul p⁻¹, add_left_neg,
        rpow_zero, one_mul, neg_mul]
      all_goals positivity
    _ = (b ^ p⁻¹)⁻¹ * ∫ x in Ioi (0:ℝ), b ^ (-p⁻¹ * q) * (x ^ q * rexp (-x ^ p)) := by
      rw [integral_comp_mul_left_Ioi (fun x => b ^ (-p⁻¹ * q) * (x ^ q * exp (- x ^ p))) 0,
        mul_zero, abs_eq_self.mpr ?_, smul_eq_mul]
      all_goals positivity
    _ = b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
      rw [integral_mul_left, integral_rpow_mul_exp_neg_rpow _ hq, mul_assoc, ← mul_assoc,
        ← rpow_neg_one, ← rpow_mul, ← rpow_add]
      congr; ring
      all_goals positivity

theorem integral_exp_neg_rpow {p : ℝ} (hp : 0 < p) :
    ∫ x in Ioi (0:ℝ), exp (- x ^ p) = Gamma (1 / p + 1) := by
  convert (integral_rpow_mul_exp_neg_rpow hp neg_one_lt_zero) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp))]

theorem integral_exp_neg_mul_rpow {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    ∫ x in Ioi (0:ℝ), exp (- b * x ^ p) = b ^ (- 1 / p) * Gamma (1 / p + 1) := by
  convert (integral_rpow_mul_exp_neg_mul_rpow hp neg_one_lt_zero hb) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp)), mul_assoc]

theorem Complex.integral_rpow_mul_exp_neg_rpow {p q : ℝ} (hp : 1 ≤ p) (hq : - 2 < q) :
    ∫ x : ℂ, ‖x‖ ^ q * rexp (- ‖x‖ ^ p) = (2 * π / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0:ℝ) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-|x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp_rw [Complex.norm_eq_abs, Complex.polardCoord_symm_abs, smul_eq_mul]
    _ = (∫ x in Ioi (0:ℝ), x * |x| ^ q * rexp (-|x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← set_integral_prod_mul, volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0:ℝ), x * |x| ^ q * rexp (-|x| ^ p) := by
      simp_rw [integral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_Ioo, sub_neg_eq_add, ← two_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * π),
        smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0:ℝ), x ^ (q + 1) * rexp (-x ^ p) := by
      congr 1
      refine set_integral_congr measurableSet_Ioi (fun x hx => ?_)
      rw [abs_eq_self.mpr (le_of_lt (by exact hx)), rpow_add hx, rpow_one]
      ring
    _ = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_rpow (by linarith) (by linarith), add_assoc,
        one_add_one_eq_two]
      ring

theorem Complex.integral_rpow_mul_exp_neg_mul_rpow {p q b : ℝ} (hp : 1 ≤ p) (hq : - 2 < q)
    (hb : 0 < b) :
    ∫ x : ℂ, ‖x‖ ^ q * rexp (- b * ‖x‖ ^ p) = (2 * π / p) *
      b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0:ℝ) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (- b * |x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp_rw [Complex.norm_eq_abs, Complex.polardCoord_symm_abs, smul_eq_mul]
    _ = (∫ x in Ioi (0:ℝ), x * |x| ^ q * rexp (- b * |x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← set_integral_prod_mul, volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0:ℝ), x * |x| ^ q * rexp (- b * |x| ^ p) := by
      simp_rw [integral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_Ioo, sub_neg_eq_add, ← two_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * π),
        smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0:ℝ), x ^ (q + 1) * rexp (-b * x ^ p) := by
      congr 1
      refine set_integral_congr measurableSet_Ioi (fun x hx => ?_)
      rw [abs_eq_self.mpr (le_of_lt (by exact hx)), rpow_add hx, rpow_one]
      ring
    _ = (2 * π / p) * b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (by linarith) (by linarith) hb, add_assoc,
        one_add_one_eq_two]
      ring

theorem Complex.integral_exp_neg_rpow {p : ℝ} (hp : 1 ≤ p) :
    ∫ x : ℂ, rexp (- ‖x‖ ^ p) = π * Real.Gamma (2 / p + 1) := by
  convert (integral_rpow_mul_exp_neg_rpow hp (by linarith : (-2:ℝ) < 0)) using 1
  · simp_rw [norm_eq_abs, rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

theorem Complex.integral_exp_neg_mul_rpow {p b : ℝ} (hp : 1 ≤ p) (hb : 0 < b) :
    ∫ x : ℂ, rexp (- b * ‖x‖ ^ p) = π * b ^ (-2 / p) * Real.Gamma (2 / p + 1) := by
  convert (integral_rpow_mul_exp_neg_mul_rpow hp (by linarith : (-2:ℝ) < 0)) hb using 1
  · simp_rw [norm_eq_abs, rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

end integrals

section move_me

open BigOperators Fintype MeasureTheory MeasureTheory.Measure

theorem MeasureTheory.integral_finset_prod_eq_pow' {E : Type*} {n : ℕ} (f : E → ℝ) [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] : ∫ x : (Fin n) → E, ∏ i, f (x i) = (∫ x, f x) ^ n := by
  induction n with
  | zero =>
      simp only [Nat.zero_eq, volume_pi, Finset.univ_eq_empty, Finset.prod_empty, integral_const,
        pi_empty_univ, ENNReal.one_toReal, smul_eq_mul, mul_one, pow_zero]
  | succ n n_ih =>
      calc
        _ = ∫ x : E × (Fin n → E), (f x.1) * ∏ i : Fin n, f (x.2 i) := by
          rw [volume_pi, ← ((measurePreserving_piFinSuccAboveEquiv
            (fun _ => (volume : Measure E)) 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAboveEquiv_symm_apply, Fin.insertNth_zero',
            Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
          rfl
        _ = (∫ x, f x) * (∫ x, f x) ^ n := by rw [← n_ih, ← integral_prod_mul, volume_eq_prod]
        _ = (∫ x, f x) ^ n.succ := by rw [← pow_succ]

theorem MeasureTheory.integral_finset_prod_eq_pow {E : Type*} (ι : Type*) [Fintype ι] (f : E → ℝ)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := by
  let p := measurePreserving_piCongrLeft (fun _ => (volume : Measure E)) (equivFin ι)
  rw [volume_pi, ← (p.symm).integral_comp', ← integral_finset_prod_eq_pow']
  congr!
  rw [Fintype.prod_equiv (equivFin ι)]
  exact fun _ => rfl

end move_me

namespace MeasureTheory

open MeasureTheory.Measure FiniteDimensional ENNReal Filter

open scoped Topology

noncomputable section main_result

theorem measure_unitBall_eq_integral_div_gamma {E : Type*} {p : ℝ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] (μ : Measure E) [IsAddHaarMeasure μ] (hp : 0 < p) :
    μ (Metric.ball 0 1) =
      .ofReal ((∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)) := by
  have : (0:ℝ) < finrank ℝ E := Nat.cast_pos.mpr finrank_pos
  have : ((∫ y in Set.Ioi (0:ℝ), y ^ (finrank ℝ E - 1) • Real.exp (-y ^ p)) /
      Real.Gamma ((finrank ℝ E) / p + 1)) * (finrank ℝ E) = 1 := by
    simp_rw [← Real.rpow_nat_cast _ (finrank ℝ E - 1), smul_eq_mul, Nat.cast_sub finrank_pos,
      Nat.cast_one]
    rw [integral_rpow_mul_exp_neg_rpow hp (by linarith), sub_add_cancel,
      Real.Gamma_add_one (ne_of_gt (by positivity))]
    field_simp; ring
  rw [integral_fun_norm_addHaar μ (fun x => Real.exp (- x ^ p)), nsmul_eq_mul, smul_eq_mul,
    mul_div_assoc, mul_div_assoc, mul_comm, mul_assoc, this, mul_one, ofReal_toReal]
  exact ne_of_lt measure_ball_lt_top

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [mE : MeasurableSpace E]
  [tE : TopologicalSpace E] [TopologicalAddGroup E] [BorelSpace E] [T2Space E] [Nontrivial E]
  [ContinuousSMul ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {g : E → ℝ} (h1 : g 0 = 0)
  (h2 : ∀ x, g (- x) = g x) (h3 : ∀ x y, g (x + y) ≤ g x + g y) (h4 : ∀ {x}, g x = 0 → x = 0)
  (h5 :  ∀ r x, g (r • x) ≤ |r| * (g x))

theorem measure_lt_one_eq_integral_div_gamma {p : ℝ} (hp : 0 < p) :
    μ {x : E | g x < 1} =
      .ofReal ((∫ (x : E), Real.exp (- (g x) ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)) := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  letI F : Type _ := E
  letI : NormedAddCommGroup F :=
  { norm := g
    dist := fun x y => g (x - y)
    dist_self := by simp only [_root_.sub_self, h1, forall_const]
    dist_comm := fun _ _ => by dsimp [dist]; rw [← h2, neg_sub]
    dist_triangle := fun x y z => by convert h3 (x - y) (y - z) using 1; abel_nf
    edist := fun x y => .ofReal (g (x - y))
    edist_dist := fun _ _ => rfl
    eq_of_dist_eq_zero := by convert fun _ _ h => eq_of_sub_eq_zero (h4 h) }
  letI : NormedSpace ℝ F :=
  { norm_smul_le := fun _ _ =>  h5 _ _ }
  -- We put the new topology on F
  letI : TopologicalSpace F := UniformSpace.toTopologicalSpace
  letI : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv ℝ _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl ℝ E : E ≃ₗ[ℝ] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify the topology of E
  let ν : Measure F := @Measure.map E F _ mE φ μ
  have : IsAddHaarMeasure ν :=
    @ContinuousLinearEquiv.isAddHaarMeasure_map E F ℝ ℝ _ _ _ _ _ _ tE _ _ _ _ _ _ _ mE _ _ _ φ μ _
  convert (measure_unitBall_eq_integral_div_gamma ν hp) using 1
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr!
      simp_rw [Metric.ball, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · -- The map between `E` and `F` as a measurable equivalence
    let ψ := @Homeomorph.toMeasurableEquiv E F tE mE _ _ _ _
      (@ContinuousLinearEquiv.toHomeomorph ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ)
    -- The map `ψ` is measure preserving by construction
    have : @MeasurePreserving E F mE _ ψ μ ν :=
      @Measurable.measurePreserving E F mE _ ψ (@MeasurableEquiv.measurable E F mE _ ψ) _
    erw [← this.integral_comp (@MeasurableEquiv.measurableEmbedding E F mE _ ψ)]
    rfl

-- TODO. I don't know how to prove that without duplicating most of the previous proof...
theorem measure_le_one_eq_integral_div_gamma {p : ℝ} (hp : 0 < p) :
    μ {x : E | g x ≤ 1} =
      .ofReal ((∫ (x : E), Real.exp (- (g x) ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)) := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  letI F : Type _ := E
  letI : NormedAddCommGroup F :=
  { norm := g
    dist := fun x y => g (x - y)
    dist_self := by simp only [_root_.sub_self, h1, forall_const]
    dist_comm := fun _ _ => by dsimp [dist]; rw [← h2, neg_sub]
    dist_triangle := fun x y z => by convert h3 (x - y) (y - z) using 1; abel_nf
    edist := fun x y => .ofReal (g (x - y))
    edist_dist := fun _ _ => rfl
    eq_of_dist_eq_zero := by convert fun _ _ h => eq_of_sub_eq_zero (h4 h) }
  letI : NormedSpace ℝ F :=
  { norm_smul_le := fun _ _ =>  h5 _ _ }
  -- We put the new topology on F
  letI : TopologicalSpace F := UniformSpace.toTopologicalSpace
  letI : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv ℝ _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl ℝ E : E ≃ₗ[ℝ] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify the topology of E
  let ν : Measure F := @Measure.map E F _ mE φ μ
  have : IsAddHaarMeasure ν :=
    @ContinuousLinearEquiv.isAddHaarMeasure_map E F ℝ ℝ _ _ _ _ _ _ tE _ _ _ _ _ _ _ mE _ _ _ φ μ _
  convert (measure_unitBall_eq_integral_div_gamma ν hp) using 1
  · rw [← addHaar_closedBall_eq_addHaar_ball,
      @Measure.map_apply E F mE _ μ φ _ _ measurableSet_closedBall]
    · congr!
      simp_rw [Metric.closedBall, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · -- The map between `E` and `F` as a measurable equivalence
    let ψ := @Homeomorph.toMeasurableEquiv E F tE mE _ _ _ _
      (@ContinuousLinearEquiv.toHomeomorph ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ)
    -- The map `ψ` is measure preserving by construction
    have : @MeasurePreserving E F mE _ ψ μ ν :=
      @Measurable.measurePreserving E F mE _ ψ (@MeasurableEquiv.measurable E F mE _ ψ) _
    erw [← this.integral_comp (@MeasurableEquiv.measurableEmbedding E F mE _ ψ)]
    rfl

end main_result

section Complex

@[simp]
theorem Complex.volume_ball (a : ℂ) (r : ℝ) :
    volume (Metric.ball a r) = NNReal.pi * .ofReal r ^ 2 := by
  obtain hr | hr := le_or_lt r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow zero_lt_two,
      mul_zero]
  · rw [addHaar_ball_of_pos _ _ hr, Metric.ball]
    simp_rw [dist_zero_right]
    rw [measure_lt_one_eq_integral_div_gamma _ norm_zero norm_neg norm_add_le norm_eq_zero.mp ?_
      zero_lt_one]
    · rw [Complex.integral_exp_neg_rpow (le_rfl), Complex.finrank_real_complex, div_one,
        Nat.cast_ofNat, div_one, mul_div_cancel, ofReal_pow (le_of_lt hr), mul_comm,
        ← NNReal.coe_real_pi, ofReal_coe_nnreal]
      exact (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))
    · intro _ _
      simp only [Complex.real_smul, norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal, le_refl]

@[simp]
theorem Complex.volume_closedBall (a : ℂ) (r : ℝ) :
    volume (Metric.closedBall a r) = NNReal.pi * .ofReal r ^ 2 := by
  rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]

end Complex

section Lp_norm

open BigOperators Real Fintype

variable (ι : Type*) [Fintype ι] [Nontrivial ι] {p : ℝ} (hp : 1 ≤ p)

theorem volume_sum_rpow_lt_one :
    volume {x : ι → ℝ | ∑ i, |x i| ^ p < 1} =
      .ofReal ((2 * Real.Gamma (1 / p + 1)) ^ card ι / Real.Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have h₂ : ∀ x : ι → ℝ, 0 ≤ ∑ i, |x i| ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg_of_nonneg (abs_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm := fun x : ι → ℝ => (PiLp.norm_eq_sum (p := .ofReal p) (f := x)
    ((toReal_ofReal (le_of_lt h₁)).symm ▸ h₁))
  simp_rw [toReal_ofReal (le_of_lt h₁), Real.norm_eq_abs] at eq_norm
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero := norm_zero (E := PiLp (.ofReal p) (fun _ : ι => ℝ))
  have eq_zero := fun x : ι → ℝ => norm_eq_zero (E := PiLp (.ofReal p) (fun _ : ι => ℝ)) (a := x)
  have nm_neg := fun x : ι → ℝ => norm_neg (E := PiLp (.ofReal p) (fun _ : ι => ℝ)) x
  have nm_add := fun x y : ι → ℝ => norm_add_le (E := PiLp (.ofReal p) (fun _ : ι => ℝ)) x y
  simp_rw [eq_norm] at eq_zero nm_zero nm_neg nm_add
  have nm_smul := fun (r : ℝ) (x : ι → ℝ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℝ)) r x
  simp_rw [eq_norm, norm_eq_abs] at nm_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert (measure_lt_one_eq_integral_div_gamma (volume : Measure (ι → ℝ))
    (g := fun x => (∑ i, |x i| ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp
    (fun r x => nm_smul r x) (by linarith : 0 < p)) using 4
  · rw [rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg_of_nonneg (abs_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, exp_sum]
    rw [integral_finset_prod_eq_pow ι fun x : ℝ => exp (- |x| ^ p), integral_comp_abs
      (f := fun x => Real.exp (- x ^ p)), integral_exp_neg_rpow h₁]
  · rw [finrank_fintype_fun_eq_card]

theorem volume_sum_rpow_lt {r p : ℝ} (hp : 1 ≤ p) (hr : 0 < r) :
    volume {x : ι → ℝ | ∑ i, |x i| ^ p < r ^ p} =
      .ofReal (r ^ (card ι) *
        (2 * Real.Gamma (1 / p + 1)) ^ card ι / Real.Gamma (card ι / p + 1)) := by
  have : 0 ≤ r ^ (card ι) := pow_nonneg (le_of_lt hr) _
  rw [mul_div_assoc, ofReal_mul this, ← volume_sum_rpow_lt_one _ hp, ← abs_eq_self.mpr this,
    ← finrank_pi ℝ]
  convert addHaar_smul volume r  {x : ι → ℝ |  ∑ i, |x i| ^ p < 1} using 2
  simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_setOf_eq, Pi.smul_apply,
    smul_eq_mul, abs_mul, mul_rpow (abs_nonneg _) (abs_nonneg _), abs_inv,
    Real.inv_rpow (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr),
    inv_mul_lt_iff (rpow_pos_of_pos hr _), mul_one]

theorem _root_.Complex.volume_sum_rpow_lt_one {p : ℝ} (hp : 1 ≤ p) :
    volume {x : ι → ℂ | ∑ i, ‖x i‖ ^ p < 1} =
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have h₂ : ∀ x : ι → ℂ, 0 ≤ ∑ i, ‖x i‖ ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg_of_nonneg (norm_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm := fun x : ι → ℂ => (PiLp.norm_eq_sum (p := .ofReal p) (f := x)
    ((toReal_ofReal (le_of_lt h₁)).symm ▸ h₁))
  simp_rw [toReal_ofReal (le_of_lt h₁)] at eq_norm
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero := norm_zero (E := PiLp (.ofReal p) (fun _ : ι => ℂ))
  have eq_zero := fun x : ι → ℂ => norm_eq_zero (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) (a := x)
  have nm_neg := fun x : ι → ℂ => norm_neg (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) x
  have nm_add := fun x y : ι → ℂ => norm_add_le (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) x y
  simp_rw [eq_norm] at eq_zero nm_zero nm_neg nm_add
  have eq_smul := fun (r : ℝ) (x : ι → ℂ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℂ)) r x
  simp_rw [eq_norm, norm_eq_abs] at eq_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert measure_lt_one_eq_integral_div_gamma (volume : Measure (ι → ℂ))
    (g := fun x => (∑ i, ‖x i‖ ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp
    (fun r x => eq_smul r x) (by linarith : 0 < p) using 4
  · rw [Real.rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg_of_nonneg (norm_nonneg _) _)
  · simp_rw [← Real.rpow_mul (h₂ _), div_mul_cancel _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [integral_finset_prod_eq_pow ι fun x : ℂ => Real.exp (- ‖x‖ ^ p),
      Complex.integral_exp_neg_rpow hp]
  · rw [finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
       Nat.cast_mul, Nat.cast_ofNat, Fintype.card, mul_comm]

theorem _root_.Complex.volume_sum_rpow_lt {r p : ℝ} (hp : 1 ≤ p) (hr : 0 < r) :
    volume {x : ι → ℝ | ∑ i, |x i| ^ p < r ^ p} =
      .ofReal (r ^ (card ι) *
        (2 * Real.Gamma (1 / p + 1)) ^ card ι / Real.Gamma (card ι / p + 1)) := by
  have : 0 ≤ r ^ (card ι) := pow_nonneg (le_of_lt hr) _
  rw [mul_div_assoc, ofReal_mul this, ← volume_sum_rpow_lt_one _ hp, ← abs_eq_self.mpr this,
    ← finrank_pi ℝ]
  convert addHaar_smul volume r  {x : ι → ℝ |  ∑ i, |x i| ^ p < 1} using 2
  simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_setOf_eq, Pi.smul_apply,
    smul_eq_mul, abs_mul, mul_rpow (abs_nonneg _) (abs_nonneg _), abs_inv,
    Real.inv_rpow (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr),
    inv_mul_lt_iff (rpow_pos_of_pos hr _), mul_one]

end Lp_norm

section Euclidean_space

@[simp]
theorem Euclidean_space.volume_ball (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (Metric.ball x r) = NNReal.pi * (.ofReal r) ^ 2 := by
  obtain hr | hr := le_total r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow zero_lt_two,
      mul_zero]
  · suffices volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = NNReal.pi by
      rw [Measure.addHaar_ball _ _ hr, finrank_euclideanSpace_fin, ofReal_pow hr, this, mul_comm]
    have := EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)
    rw [EuclideanSpace.ball_zero_eq _ zero_le_one, one_pow, ← (this.symm).measure_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), Set.preimage_setOf_eq]
    convert (volume_sum_rpow_lt_one (Fin 2) one_le_two)
    · rw [Real.rpow_two, ← abs_pow, abs_sq]
      rfl
    · rw [Fintype.card_fin, Nat.cast_ofNat, div_self two_ne_zero, one_add_one_eq_two,
      Real.Gamma_two, div_one, Real.Gamma_add_one (by norm_num), ← mul_assoc, mul_div_cancel' _
      two_ne_zero, one_mul, Real.Gamma_one_half_eq, Real.sq_sqrt (by positivity),
      ← NNReal.coe_real_pi, ofReal_coe_nnreal]

end Euclidean_space

end MeasureTheory
