/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Volume of balls

Let `E` be a finite dimensional normed `ℝ`-vector space equipped with a Haar measure `μ`. We
prove that
`μ (Metric.ball 0 1) = (∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)`
for any real number `p` with `0 < p`, see `MeasureTheorymeasure_unitBall_eq_integral_div_gamma`. We
also prove the corresponding result to compute `μ {x : E | g x < 1}` where `g : E → ℝ` is a function
defining a norm on `E`, see `MeasureTheory.measure_lt_one_eq_integral_div_gamma`.

Using these formulas, we compute the volume of the unit balls in several cases.

* `MeasureTheory.volume_sum_rpow_lt` / `MeasureTheory.volume_sum_rpow_le`: volume of the open and
  closed balls for the norm `Lp` over a real finite dimensional vector space with `1 ≤ p`. These
  are computed as `volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r}` and
  `volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r}` since the spaces `PiLp` do not have a
  `MeasureSpace` instance.

* `Complex.volume_sum_rpow_lt_one` / `Complex.volume_sum_rpow_lt`: same as above but for complex
  finite dimensional vector space.

* `EuclideanSpace.volume_ball` / `EuclideanSpace.volume_closedBall` : volume of open and closed
  balls in a finite dimensional Euclidean space.

* `InnerProductSpace.volume_ball` / `InnerProductSpace.volume_closedBall`: volume of open and closed
  balls in a finite dimensional real inner product space.

* `Complex.volume_ball` / `Complex.volume_closedBall`: volume of open and closed balls in `ℂ`.
-/

section general_case

open MeasureTheory MeasureTheory.Measure FiniteDimensional ENNReal

theorem MeasureTheory.measure_unitBall_eq_integral_div_gamma {E : Type*} {p : ℝ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (hp : 0 < p) :
    μ (Metric.ball 0 1) =
      .ofReal ((∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)) := by
  obtain hE | hE := subsingleton_or_nontrivial E
  · rw [(Metric.nonempty_ball.mpr zero_lt_one).eq_zero, ← integral_univ, Set.univ_nonempty.eq_zero,
      integral_singleton, finrank_zero_of_subsingleton, Nat.cast_zero, zero_div, zero_add,
      Real.Gamma_one, div_one, norm_zero, Real.zero_rpow (ne_of_gt hp), neg_zero, Real.exp_zero,
      smul_eq_mul, mul_one, ofReal_toReal (measure_ne_top μ {0})]
  · have : (0:ℝ) < finrank ℝ E := Nat.cast_pos.mpr finrank_pos
    have : ((∫ y in Set.Ioi (0:ℝ), y ^ (finrank ℝ E - 1) • Real.exp (-y ^ p)) /
        Real.Gamma ((finrank ℝ E) / p + 1)) * (finrank ℝ E) = 1 := by
      simp_rw [← Real.rpow_natCast _ (finrank ℝ E - 1), smul_eq_mul, Nat.cast_sub finrank_pos,
        Nat.cast_one]
      rw [integral_rpow_mul_exp_neg_rpow hp (by linarith), sub_add_cancel,
        Real.Gamma_add_one (ne_of_gt (by positivity))]
      field_simp; ring
    rw [integral_fun_norm_addHaar μ (fun x => Real.exp (- x ^ p)), nsmul_eq_mul, smul_eq_mul,
      mul_div_assoc, mul_div_assoc, mul_comm, mul_assoc, this, mul_one, ofReal_toReal]
    exact ne_of_lt measure_ball_lt_top

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [mE : MeasurableSpace E]
  [tE : TopologicalSpace E] [TopologicalAddGroup E] [BorelSpace E] [T2Space E] [ContinuousSMul ℝ E]
  (μ : Measure E) [IsAddHaarMeasure μ] {g : E → ℝ} (h1 : g 0 = 0) (h2 : ∀ x, g (- x) = g x)
  (h3 : ∀ x y, g (x + y) ≤ g x + g y) (h4 : ∀ {x}, g x = 0 → x = 0)
  (h5 : ∀ r x, g (r • x) ≤ |r| * (g x))

theorem MeasureTheory.measure_lt_one_eq_integral_div_gamma {p : ℝ} (hp : 0 < p) :
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
  { norm_smul_le := fun _ _ ↦ h5 _ _ }
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
    erw [← this.integral_comp']
    rfl

theorem MeasureTheory.measure_le_eq_lt [Nontrivial E] (r : ℝ) :
    μ {x : E | g x ≤ r} = μ {x : E | g x < r} := by
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
  { norm_smul_le := fun _ _ ↦ h5 _ _ }
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
  convert addHaar_closedBall_eq_addHaar_ball ν 0 r using 1
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_closedBall]
    · congr!
      simp_rw [Metric.closedBall, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr!
      simp_rw [Metric.ball, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ

end general_case

section LpSpace

open Real Fintype ENNReal FiniteDimensional MeasureTheory MeasureTheory.Measure

variable (ι : Type*) [Fintype ι] {p : ℝ} (hp : 1 ≤ p)

theorem MeasureTheory.volume_sum_rpow_lt_one :
    volume {x : ι → ℝ | ∑ i, |x i| ^ p < 1} =
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have h₂ : ∀ x : ι → ℝ, 0 ≤ ∑ i, |x i| ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (abs_nonneg _) _) _
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
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg (abs_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel₀ _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, exp_sum]
    rw [integral_fintype_prod_eq_pow ι fun x : ℝ => exp (- |x| ^ p), integral_comp_abs
      (f := fun x => exp (- x ^ p)), integral_exp_neg_rpow h₁]
  · rw [finrank_fintype_fun_eq_card]

theorem MeasureTheory.volume_sum_rpow_lt [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r} = (.ofReal r) ^ card ι *
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : ∀ x : ι → ℝ, 0 ≤ ∑ i, |x i| ^ p := by
      refine fun _ => Finset.sum_nonneg' ?_
      exact fun i => (fun _ => rpow_nonneg (abs_nonneg _) _) _
  have h₂ : ∀ x : ι → ℝ, 0 ≤ (∑ i, |x i| ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_lt r 0
  · have : {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact not_le.mpr (lt_of_lt_of_le (Set.mem_setOf.mp hx) hr) (h₂ x)
    rw [this, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow Fin.size_pos'.ne', zero_mul]
  · rw [← volume_sum_rpow_lt_one _ hp, ← ofReal_pow (le_of_lt hr), ← finrank_pi ℝ]
    convert addHaar_smul_of_nonneg volume (le_of_lt hr) {x : ι → ℝ | ∑ i, |x i| ^ p < 1} using 2
    simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_setOf_eq, Pi.smul_apply,
      smul_eq_mul, abs_mul, mul_rpow (abs_nonneg _) (abs_nonneg _), abs_inv,
      inv_rpow (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr),
      inv_mul_lt_iff (rpow_pos_of_pos hr _), mul_one, ← rpow_lt_rpow_iff
      (rpow_nonneg (h₁ _) _) (le_of_lt hr) (by linarith : 0 < p), ← rpow_mul
      (h₁ _), div_mul_cancel₀ _ (ne_of_gt (by linarith) : p ≠ 0), Real.rpow_one]

theorem MeasureTheory.volume_sum_rpow_le [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r} = (.ofReal r) ^ card ι *
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  -- We collect facts about `Lp` norms that will be used in `measure_le_one_eq_lt_one`
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
  rw [measure_le_eq_lt _ nm_zero (fun x ↦ nm_neg x) (fun x y ↦ nm_add x y) (eq_zero _).mp
    (fun r x => nm_smul r x), volume_sum_rpow_lt _ hp]

theorem Complex.volume_sum_rpow_lt_one {p : ℝ} (hp : 1 ≤ p) :
    volume {x : ι → ℂ | ∑ i, ‖x i‖ ^ p < 1} =
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have h₂ : ∀ x : ι → ℂ, 0 ≤ ∑ i, ‖x i‖ ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (norm_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm := fun x : ι → ℂ => (PiLp.norm_eq_sum (p := .ofReal p) (f := x)
    ((toReal_ofReal (le_of_lt h₁)).symm ▸ h₁))
  simp_rw [toReal_ofReal (le_of_lt h₁)] at eq_norm
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ENNReal.ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero := norm_zero (E := PiLp (.ofReal p) (fun _ : ι => ℂ))
  have eq_zero := fun x : ι → ℂ => norm_eq_zero (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) (a := x)
  have nm_neg := fun x : ι → ℂ => norm_neg (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) x
  have nm_add := fun x y : ι → ℂ => norm_add_le (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) x y
  simp_rw [eq_norm] at eq_zero nm_zero nm_neg nm_add
  have nm_smul := fun (r : ℝ) (x : ι → ℂ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℂ)) r x
  simp_rw [eq_norm, norm_eq_abs] at nm_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert measure_lt_one_eq_integral_div_gamma (volume : Measure (ι → ℂ))
    (g := fun x => (∑ i, ‖x i‖ ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp
    (fun r x => nm_smul r x) (by linarith : 0 < p) using 4
  · rw [rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg (norm_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel₀ _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [integral_fintype_prod_eq_pow ι fun x : ℂ => Real.exp (- ‖x‖ ^ p),
      Complex.integral_exp_neg_rpow hp]
  · rw [finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat, Fintype.card, mul_comm]

theorem Complex.volume_sum_rpow_lt [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℂ | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = (.ofReal r) ^ (2 * card ι) *
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : ∀ x : ι → ℂ, 0 ≤ ∑ i, ‖x i‖ ^ p := by
      refine fun _ => Finset.sum_nonneg' ?_
      exact fun i => (fun _ => rpow_nonneg (norm_nonneg _) _) _
  have h₂ : ∀ x : ι → ℂ, 0 ≤ (∑ i, ‖x i‖ ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_lt r 0
  · have : {x : ι → ℂ | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact not_le.mpr (lt_of_lt_of_le (Set.mem_setOf.mp hx) hr) (h₂ x)
    rw [this, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow Fin.size_pos'.ne', zero_mul]
  · rw [← Complex.volume_sum_rpow_lt_one _ hp, ← ENNReal.ofReal_pow (le_of_lt hr)]
    convert addHaar_smul_of_nonneg volume (le_of_lt hr) {x : ι → ℂ |  ∑ i, ‖x i‖ ^ p < 1} using 2
    · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_setOf_eq, Pi.smul_apply,
        norm_smul, mul_rpow (norm_nonneg _) (norm_nonneg _), Real.norm_eq_abs, abs_inv, inv_rpow
        (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr), inv_mul_lt_iff
        (rpow_pos_of_pos hr _), mul_one, ← rpow_lt_rpow_iff (rpow_nonneg (h₁ _) _)
        (le_of_lt hr) (by linarith : 0 < p), ← rpow_mul (h₁ _), div_mul_cancel₀ _
        (ne_of_gt (by linarith) : p ≠ 0), Real.rpow_one]
    · simp_rw [finrank_pi_fintype ℝ, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
        mul_comm, Fintype.card]

theorem Complex.volume_sum_rpow_le [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℂ | (∑ i, ‖x i‖ ^ p) ^ (1 / p) ≤ r} = (.ofReal r) ^ (2 * card ι) *
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm := fun x : ι → ℂ => (PiLp.norm_eq_sum (p := .ofReal p) (f := x)
    ((toReal_ofReal (le_of_lt h₁)).symm ▸ h₁))
  simp_rw [toReal_ofReal (le_of_lt h₁)] at eq_norm
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ENNReal.ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero := norm_zero (E := PiLp (.ofReal p) (fun _ : ι => ℂ))
  have eq_zero := fun x : ι → ℂ => norm_eq_zero (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) (a := x)
  have nm_neg := fun x : ι → ℂ => norm_neg (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) x
  have nm_add := fun x y : ι → ℂ => norm_add_le (E := PiLp (.ofReal p) (fun _ : ι => ℂ)) x y
  simp_rw [eq_norm] at eq_zero nm_zero nm_neg nm_add
  have nm_smul := fun (r : ℝ) (x : ι → ℂ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℂ)) r x
  simp_rw [eq_norm, norm_eq_abs] at nm_smul
  rw [measure_le_eq_lt _ nm_zero (fun x ↦ nm_neg x) (fun x y ↦ nm_add x y) (eq_zero _).mp
    (fun r x => nm_smul r x), Complex.volume_sum_rpow_lt _ hp]

end LpSpace

section EuclideanSpace

variable (ι : Type*) [Nonempty ι] [Fintype ι]

open Fintype Real MeasureTheory MeasureTheory.Measure ENNReal

theorem EuclideanSpace.volume_ball (x : EuclideanSpace ℝ ι) (r : ℝ) :
    volume (Metric.ball x r) = (.ofReal r) ^ card ι *
      .ofReal (Real.sqrt π ^ card ι / Gamma (card ι / 2 + 1)) := by
  obtain hr | hr := le_total r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow card_ne_zero,
      zero_mul]
  · suffices volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1) =
        .ofReal (Real.sqrt π ^ card ι / Gamma (card ι / 2 + 1)) by
      rw [Measure.addHaar_ball _ _ hr, this, ofReal_pow hr, finrank_euclideanSpace]
    rw [← ((EuclideanSpace.volume_preserving_measurableEquiv _).symm).measure_preimage
      measurableSet_ball]
    convert (volume_sum_rpow_lt_one ι one_le_two) using 4
    · simp_rw [EuclideanSpace.ball_zero_eq _ zero_le_one, one_pow, Real.rpow_two, sq_abs,
        Set.setOf_app_iff]
    · rw [Gamma_add_one (by norm_num), Gamma_one_half_eq, ← mul_assoc, mul_div_cancel₀ _
        two_ne_zero, one_mul]

theorem EuclideanSpace.volume_closedBall (x : EuclideanSpace ℝ ι) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ card ι *
      .ofReal (sqrt π ^ card ι / Gamma (card ι / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball, EuclideanSpace.volume_ball]

-- 2024-04-06
@[deprecated] alias Euclidean_space.volume_ball := EuclideanSpace.volume_ball
@[deprecated] alias Euclidean_space.volume_closedBall := EuclideanSpace.volume_closedBall

end EuclideanSpace

section InnerProductSpace

open MeasureTheory MeasureTheory.Measure ENNReal Real FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem InnerProductSpace.volume_ball (x : E) (r : ℝ) :
    volume (Metric.ball x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (sqrt π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1)) := by
  rw [← ((stdOrthonormalBasis ℝ E).measurePreserving_repr_symm).measure_preimage
      measurableSet_ball]
  have : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.mp finrank_pos
  have := EuclideanSpace.volume_ball (Fin (finrank ℝ E)) ((stdOrthonormalBasis ℝ E).repr x) r
  simp_rw [Fintype.card_fin] at this
  convert this
  simp only [LinearIsometryEquiv.preimage_ball, LinearIsometryEquiv.symm_symm, _root_.map_zero]

theorem InnerProductSpace.volume_closedBall (x : E) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (sqrt π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball, InnerProductSpace.volume_ball _]

end InnerProductSpace

section Complex

open MeasureTheory MeasureTheory.Measure ENNReal

@[simp]
theorem Complex.volume_ball (a : ℂ) (r : ℝ) :
    volume (Metric.ball a r) = .ofReal r ^ 2 * NNReal.pi := by
  rw [InnerProductSpace.volume_ball a r, finrank_real_complex, Nat.cast_ofNat, div_self two_ne_zero,
    one_add_one_eq_two, Real.Gamma_two, div_one, Real.sq_sqrt (by positivity),
    ← NNReal.coe_real_pi, ofReal_coe_nnreal]

@[simp]
theorem Complex.volume_closedBall (a : ℂ) (r : ℝ) :
    volume (Metric.closedBall a r) = .ofReal r ^ 2 * NNReal.pi := by
  rw [addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]

end Complex
