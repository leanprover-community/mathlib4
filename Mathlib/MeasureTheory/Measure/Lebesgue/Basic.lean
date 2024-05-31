/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

#align_import measure_theory.measure.lebesgue.basic from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We show that the Lebesgue measure on the real line (constructed as a particular case of additive
Haar measure on inner product spaces) coincides with the Stieltjes measure associated
to the function `x ↦ x`. We deduce properties of this measure on `ℝ`, and then of the product
Lebesgue measure on `ℝⁿ`. In particular, we prove that they are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`, where they are proved more generally for any
additive Haar measure on a finite-dimensional real vector space.
-/


assert_not_exists MeasureTheory.integral

noncomputable section

open scoped Classical
open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/


namespace Real

variable {ι : Type*} [Fintype ι]

/-- The volume on the real line (as a particular case of the volume on a finite-dimensional
inner product space) coincides with the Stieltjes measure coming from the identity function. -/
theorem volume_eq_stieltjes_id : (volume : Measure ℝ) = StieltjesFunction.id.measure := by
  haveI : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
      Eq.symm <|
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis ℝ ℝ)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis ℝ ℝ) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped, A]
  simp only [volume, Basis.addHaar, one_smul]
#align real.volume_eq_stieltjes_id Real.volume_eq_stieltjes_id

theorem volume_val (s) : volume s = StieltjesFunction.id.measure s := by
  simp [volume_eq_stieltjes_id]
#align real.volume_val Real.volume_val

@[simp]
theorem volume_Ico {a b : ℝ} : volume (Ico a b) = ofReal (b - a) := by simp [volume_val]
#align real.volume_Ico Real.volume_Ico

@[simp]
theorem volume_Icc {a b : ℝ} : volume (Icc a b) = ofReal (b - a) := by simp [volume_val]
#align real.volume_Icc Real.volume_Icc

@[simp]
theorem volume_Ioo {a b : ℝ} : volume (Ioo a b) = ofReal (b - a) := by simp [volume_val]
#align real.volume_Ioo Real.volume_Ioo

@[simp]
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = ofReal (b - a) := by simp [volume_val]
#align real.volume_Ioc Real.volume_Ioc

-- @[simp] -- Porting note (#10618): simp can prove this
theorem volume_singleton {a : ℝ} : volume ({a} : Set ℝ) = 0 := by simp [volume_val]
#align real.volume_singleton Real.volume_singleton

-- @[simp] -- Porting note (#10618): simp can prove this, after mathlib4#4628
theorem volume_univ : volume (univ : Set ℝ) = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : ℝ≥0∞) = volume (Icc (0 : ℝ) r) := by simp
      _ ≤ volume univ := measure_mono (subset_univ _)
#align real.volume_univ Real.volume_univ

@[simp]
theorem volume_ball (a r : ℝ) : volume (Metric.ball a r) = ofReal (2 * r) := by
  rw [ball_eq_Ioo, volume_Ioo, ← sub_add, add_sub_cancel_left, two_mul]
#align real.volume_ball Real.volume_ball

@[simp]
theorem volume_closedBall (a r : ℝ) : volume (Metric.closedBall a r) = ofReal (2 * r) := by
  rw [closedBall_eq_Icc, volume_Icc, ← sub_add, add_sub_cancel_left, two_mul]
#align real.volume_closed_ball Real.volume_closedBall

@[simp]
theorem volume_emetric_ball (a : ℝ) (r : ℝ≥0∞) : volume (EMetric.ball a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.emetric_ball_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.emetric_ball_nnreal, volume_ball, two_mul, ← NNReal.coe_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, two_mul]
#align real.volume_emetric_ball Real.volume_emetric_ball

@[simp]
theorem volume_emetric_closedBall (a : ℝ) (r : ℝ≥0∞) : volume (EMetric.closedBall a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [EMetric.closedBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.emetric_closedBall_nnreal, volume_closedBall, two_mul, ← NNReal.coe_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, two_mul]
#align real.volume_emetric_closed_ball Real.volume_emetric_closedBall

instance noAtoms_volume : NoAtoms (volume : Measure ℝ) :=
  ⟨fun _ => volume_singleton⟩
#align real.has_no_atoms_volume Real.noAtoms_volume

@[simp]
theorem volume_interval {a b : ℝ} : volume (uIcc a b) = ofReal |b - a| := by
  rw [← Icc_min_max, volume_Icc, max_sub_min_eq_abs]
#align real.volume_interval Real.volume_interval

@[simp]
theorem volume_Ioi {a : ℝ} : volume (Ioi a) = ∞ :=
  top_unique <|
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo a (a + n)) := by simp
        _ ≤ volume (Ioi a) := measure_mono Ioo_subset_Ioi_self
#align real.volume_Ioi Real.volume_Ioi

@[simp]
theorem volume_Ici {a : ℝ} : volume (Ici a) = ∞ := by rw [← measure_congr Ioi_ae_eq_Ici]; simp
#align real.volume_Ici Real.volume_Ici

@[simp]
theorem volume_Iio {a : ℝ} : volume (Iio a) = ∞ :=
  top_unique <|
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo (a - n) a) := by simp
        _ ≤ volume (Iio a) := measure_mono Ioo_subset_Iio_self
#align real.volume_Iio Real.volume_Iio

@[simp]
theorem volume_Iic {a : ℝ} : volume (Iic a) = ∞ := by rw [← measure_congr Iio_ae_eq_Iic]; simp
#align real.volume_Iic Real.volume_Iic

instance locallyFinite_volume : IsLocallyFiniteMeasure (volume : Measure ℝ) :=
  ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]⟩⟩
#align real.locally_finite_volume Real.locallyFinite_volume

instance isFiniteMeasure_restrict_Icc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Icc x y)) :=
  ⟨by simp⟩
#align real.is_finite_measure_restrict_Icc Real.isFiniteMeasure_restrict_Icc

instance isFiniteMeasure_restrict_Ico (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ico x y)) :=
  ⟨by simp⟩
#align real.is_finite_measure_restrict_Ico Real.isFiniteMeasure_restrict_Ico

instance isFiniteMeasure_restrict_Ioc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioc x y)) :=
  ⟨by simp⟩
#align real.is_finite_measure_restrict_Ioc Real.isFiniteMeasure_restrict_Ioc

instance isFiniteMeasure_restrict_Ioo (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioo x y)) :=
  ⟨by simp⟩
#align real.is_finite_measure_restrict_Ioo Real.isFiniteMeasure_restrict_Ioo

theorem volume_le_diam (s : Set ℝ) : volume s ≤ EMetric.diam s := by
  by_cases hs : Bornology.IsBounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono (Real.subset_Icc_sInf_sSup_of_isBounded hs)
  · rw [Metric.ediam_of_unbounded hs]; exact le_top
#align real.volume_le_diam Real.volume_le_diam

theorem _root_.Filter.Eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ}
    (h : ∀ᶠ x in 𝓝 a, p x) : (0 : ℝ≥0∞) < volume { x | p x } := by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  refine lt_of_lt_of_le ?_ (measure_mono hs)
  simpa [-mem_Ioo] using hx.1.trans hx.2
#align filter.eventually.volume_pos_of_nhds_real Filter.Eventually.volume_pos_of_nhds_real

/-!
### Volume of a box in `ℝⁿ`
-/


theorem volume_Icc_pi {a b : ι → ℝ} : volume (Icc a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [← pi_univ_Icc, volume_pi_pi]
  simp only [Real.volume_Icc]
#align real.volume_Icc_pi Real.volume_Icc_pi

@[simp]
theorem volume_Icc_pi_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (Icc a b)).toReal = ∏ i, (b i - a i) := by
  simp only [volume_Icc_pi, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
#align real.volume_Icc_pi_to_real Real.volume_Icc_pi_toReal

theorem volume_pi_Ioo {a b : ι → ℝ} :
    volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi
#align real.volume_pi_Ioo Real.volume_pi_Ioo

@[simp]
theorem volume_pi_Ioo_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ioo (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioo, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
#align real.volume_pi_Ioo_to_real Real.volume_pi_Ioo_toReal

theorem volume_pi_Ioc {a b : ι → ℝ} :
    volume (pi univ fun i => Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi
#align real.volume_pi_Ioc Real.volume_pi_Ioc

@[simp]
theorem volume_pi_Ioc_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
#align real.volume_pi_Ioc_to_real Real.volume_pi_Ioc_toReal

theorem volume_pi_Ico {a b : ι → ℝ} :
    volume (pi univ fun i => Ico (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi
#align real.volume_pi_Ico Real.volume_pi_Ico

@[simp]
theorem volume_pi_Ico_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ico (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ico, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
#align real.volume_pi_Ico_to_real Real.volume_pi_Ico_toReal

@[simp]
nonrec theorem volume_pi_ball (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_ball a hr, volume_ball, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) _).symm
#align real.volume_pi_ball Real.volume_pi_ball

@[simp]
nonrec theorem volume_pi_closedBall (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm
#align real.volume_pi_closed_ball Real.volume_pi_closedBall

theorem volume_pi_le_prod_diam (s : Set (ι → ℝ)) :
    volume s ≤ ∏ i : ι, EMetric.diam (Function.eval i '' s) :=
  calc
    volume s ≤ volume (pi univ fun i => closure (Function.eval i '' s)) :=
      volume.mono <|
        Subset.trans (subset_pi_eval_image univ s) <| pi_mono fun _ _ => subset_closure
    _ = ∏ i, volume (closure <| Function.eval i '' s) := volume_pi_pi _
    _ ≤ ∏ i : ι, EMetric.diam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun _ _ => (volume_le_diam _).trans_eq (EMetric.diam_closure _)
#align real.volume_pi_le_prod_diam Real.volume_pi_le_prod_diam

theorem volume_pi_le_diam_pow (s : Set (ι → ℝ)) : volume s ≤ EMetric.diam s ^ Fintype.card ι :=
  calc
    volume s ≤ ∏ i : ι, EMetric.diam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ ≤ ∏ _i : ι, (1 : ℝ≥0) * EMetric.diam s :=
      (Finset.prod_le_prod' fun i _ => (LipschitzWith.eval i).ediam_image_le s)
    _ = EMetric.diam s ^ Fintype.card ι := by
      simp only [ENNReal.coe_one, one_mul, Finset.prod_const, Fintype.card]
#align real.volume_pi_le_diam_pow Real.volume_pi_le_diam_pow

/-!
### Images of the Lebesgue measure under multiplication in ℝ
-/


theorem smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    ENNReal.ofReal |a| • Measure.map (a * ·) volume = volume := by
  refine (Real.measure_ext_Ioo_rat fun p q => ?_).symm
  cases' lt_or_gt_of_ne h with h h
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt <| neg_pos.2 h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, neg_sub_neg, neg_mul,
      preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub, smul_eq_mul,
      mul_div_cancel₀ _ (ne_of_lt h)]
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, preimage_const_mul_Ioo _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel₀ _ (ne_of_gt h), smul_eq_mul]
#align real.smul_map_volume_mul_left Real.smul_map_volume_mul_left

theorem map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    Measure.map (a * ·) volume = ENNReal.ofReal |a⁻¹| • volume := by
  conv_rhs =>
    rw [← Real.smul_map_volume_mul_left h, smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ←
      abs_mul, inv_mul_cancel h, abs_one, ENNReal.ofReal_one, one_smul]
#align real.map_volume_mul_left Real.map_volume_mul_left

@[simp]
theorem volume_preimage_mul_left {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
    volume ((a * ·) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((a * ·) ⁻¹' s) = Measure.map (a * ·) volume s :=
      ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_left h]; rfl
#align real.volume_preimage_mul_left Real.volume_preimage_mul_left

theorem smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
    ENNReal.ofReal |a| • Measure.map (· * a) volume = volume := by
  simpa only [mul_comm] using Real.smul_map_volume_mul_left h
#align real.smul_map_volume_mul_right Real.smul_map_volume_mul_right

theorem map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
    Measure.map (· * a) volume = ENNReal.ofReal |a⁻¹| • volume := by
  simpa only [mul_comm] using Real.map_volume_mul_left h
#align real.map_volume_mul_right Real.map_volume_mul_right

@[simp]
theorem volume_preimage_mul_right {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
    volume ((· * a) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((· * a) ⁻¹' s) = Measure.map (· * a) volume s :=
      ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_right h]; rfl
#align real.volume_preimage_mul_right Real.volume_preimage_mul_right

/-!
### Images of the Lebesgue measure under translation/linear maps in ℝⁿ
-/


open Matrix

/-- A diagonal matrix rescales Lebesgue according to its determinant. This is a special case of
`Real.map_matrix_volume_pi_eq_smul_volume_pi`, that one should use instead (and whose proof
uses this particular case). -/
theorem smul_map_diagonal_volume_pi [DecidableEq ι] {D : ι → ℝ} (h : det (diagonal D) ≠ 0) :
    ENNReal.ofReal (abs (det (diagonal D))) • Measure.map (toLin' (diagonal D)) volume =
      volume := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  simp only [det_diagonal, Measure.coe_smul, Algebra.id.smul_eq_mul, Pi.smul_apply]
  rw [Measure.map_apply _ (MeasurableSet.univ_pi hs)]
  swap; · exact Continuous.measurable (LinearMap.continuous_on_pi _)
  have :
    (Matrix.toLin' (diagonal D) ⁻¹' Set.pi Set.univ fun i : ι => s i) =
      Set.pi Set.univ fun i : ι => (D i * ·) ⁻¹' s i := by
    ext f
    simp only [LinearMap.coe_proj, Algebra.id.smul_eq_mul, LinearMap.smul_apply, mem_univ_pi,
      mem_preimage, LinearMap.pi_apply, diagonal_toLin']
  have B : ∀ i, ofReal (abs (D i)) * volume ((D i * ·) ⁻¹' s i) = volume (s i) := by
    intro i
    have A : D i ≠ 0 := by
      simp only [det_diagonal, Ne] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [volume_preimage_mul_left A, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
      mul_inv_cancel A, abs_one, ENNReal.ofReal_one, one_mul]
  rw [this, volume_pi_pi, Finset.abs_prod,
    ENNReal.ofReal_prod_of_nonneg fun i _ => abs_nonneg (D i), ← Finset.prod_mul_distrib]
  simp only [B]
#align real.smul_map_diagonal_volume_pi Real.smul_map_diagonal_volume_pi

/-- A transvection preserves Lebesgue measure. -/
theorem volume_preserving_transvectionStruct [DecidableEq ι] (t : TransvectionStruct ι ℝ) :
    MeasurePreserving (toLin' t.toMatrix) := by
  /- We use `lmarginal` to conveniently use Fubini's theorem.
    Along the coordinate where there is a shearing, it acts like a
    translation, and therefore preserves Lebesgue. -/
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ ↦ hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht, volume_pi]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, mulVec_stdBasisMatrix, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]
#align real.volume_preserving_transvection_struct Real.volume_preserving_transvectionStruct

/-- Any invertible matrix rescales Lebesgue measure through the absolute value of its
determinant. -/
theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : det M ≠ 0) :
    Measure.map (toLin' M) volume = ENNReal.ofReal (abs (det M)⁻¹) • volume := by
  -- This follows from the cases we have already proved, of diagonal matrices and transvections,
  -- as these matrices generate all invertible matrices.
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    conv_rhs => rw [← smul_map_diagonal_volume_pi hD]
    rw [smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel hD, abs_one,
      ENNReal.ofReal_one, one_smul]
  · intro t
    simp_rw [Matrix.TransvectionStruct.det, _root_.inv_one, abs_one, ENNReal.ofReal_one, one_smul,
      (volume_preserving_transvectionStruct _).map_eq]
  · intro A B _ _ IHA IHB
    rw [toLin'_mul, det_mul, LinearMap.coe_comp, ← Measure.map_map, IHB, Measure.map_smul, IHA,
      smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_comm, mul_inv]
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
#align real.map_matrix_volume_pi_eq_smul_volume_pi Real.map_matrix_volume_pi_eq_smul_volume_pi

/-- Any invertible linear map rescales Lebesgue measure through the absolute value of its
determinant. -/
theorem map_linearMap_volume_pi_eq_smul_volume_pi {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ}
    (hf : LinearMap.det f ≠ 0) : Measure.map f volume =
      ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • volume := by
  classical
    -- this is deduced from the matrix case
    let M := LinearMap.toMatrix' f
    have A : LinearMap.det f = det M := by simp only [M, LinearMap.det_toMatrix']
    have B : f = toLin' M := by simp only [M, toLin'_toMatrix']
    rw [A, B]
    apply map_matrix_volume_pi_eq_smul_volume_pi
    rwa [A] at hf
#align real.map_linear_map_volume_pi_eq_smul_volume_pi Real.map_linearMap_volume_pi_eq_smul_volume_pi

end Real

section regionBetween

variable {α : Type*}

/-- The region between two real-valued functions on an arbitrary set. -/
def regionBetween (f g : α → ℝ) (s : Set α) : Set (α × ℝ) :=
  { p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1) }
#align region_between regionBetween

theorem regionBetween_subset (f g : α → ℝ) (s : Set α) : regionBetween f g s ⊆ s ×ˢ univ := by
  simpa only [prod_univ, regionBetween, Set.preimage, setOf_subset_setOf] using fun a => And.left
#align region_between_subset regionBetween_subset

variable [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {s : Set α}

/-- The region between two measurable functions on a measurable set is measurable. -/
theorem measurableSet_regionBetween (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet (regionBetween f g s) := by
  dsimp only [regionBetween, Ioo, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs
#align measurable_set_region_between measurableSet_regionBetween

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the upper function. -/
theorem measurableSet_region_between_oc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ioc, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs
#align measurable_set_region_between_oc measurableSet_region_between_oc

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the lower function. -/
theorem measurableSet_region_between_co (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ico, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs
#align measurable_set_region_between_co measurableSet_region_between_co

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graphs of both functions. -/
theorem measurableSet_region_between_cc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Icc, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs
#align measurable_set_region_between_cc measurableSet_region_between_cc

/-- The graph of a measurable function is a measurable set. -/
theorem measurableSet_graph (hf : Measurable f) :
    MeasurableSet { p : α × ℝ | p.snd = f p.fst } := by
  simpa using measurableSet_region_between_cc hf hf MeasurableSet.univ
#align measurable_set_graph measurableSet_graph

theorem volume_regionBetween_eq_lintegral' (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  classical
    rw [Measure.prod_apply]
    · have h :
        (fun x => volume { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) }) =
          s.indicator fun x => ENNReal.ofReal (g x - f x) := by
        funext x
        rw [indicator_apply]
        split_ifs with h
        · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = Ioo (f x) (g x) := by simp [h, Ioo]
          simp only [hx, Real.volume_Ioo, sub_zero]
        · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = ∅ := by simp [h]
          simp only [hx, measure_empty]
      dsimp only [regionBetween, preimage_setOf_eq]
      rw [h, lintegral_indicator] <;> simp only [hs, Pi.sub_apply]
    · exact measurableSet_regionBetween hf hg hs
#align volume_region_between_eq_lintegral' volume_regionBetween_eq_lintegral'

/-- The volume of the region between two almost everywhere measurable functions on a measurable set
    can be represented as a Lebesgue integral. -/
theorem volume_regionBetween_eq_lintegral [SigmaFinite μ] (hf : AEMeasurable f (μ.restrict s))
    (hg : AEMeasurable g (μ.restrict s)) (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  have h₁ :
    (fun y => ENNReal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      ENNReal.ofReal ((AEMeasurable.mk g hg - AEMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp ENNReal.ofReal
  have h₂ :
    (μ.restrict s).prod volume (regionBetween f g s) =
      (μ.restrict s).prod volume
        (regionBetween (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s) := by
    apply measure_congr
    apply EventuallyEq.rfl.inter
    exact
      ((quasiMeasurePreserving_fst.ae_eq_comp hf.ae_eq_mk).comp₂ _ EventuallyEq.rfl).inter
        (EventuallyEq.rfl.comp₂ _ <| quasiMeasurePreserving_fst.ae_eq_comp hg.ae_eq_mk)
  rw [lintegral_congr_ae h₁, ←
    volume_regionBetween_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert h₂ using 1
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (Measure.restrict_eq_self _ (regionBetween_subset f g s)).symm
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact
      (Measure.restrict_eq_self _
          (regionBetween_subset (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s)).symm
#align volume_region_between_eq_lintegral volume_regionBetween_eq_lintegral

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable. -/
lemma nullMeasurableSet_regionBetween (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ioo (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (AEMeasurable.fst f_mble) measurable_snd.aemeasurable
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst g_mble)

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable;
a version for the region together with the graph of the upper function. -/
lemma nullMeasurableSet_region_between_oc (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (AEMeasurable.fst f_mble) measurable_snd.aemeasurable
  · change NullMeasurableSet {p : α × ℝ | p.snd ≤ g p.fst} (μ.prod volume)
    rw [show {p : α × ℝ | p.snd ≤ g p.fst} = {p : α × ℝ | g p.fst < p.snd}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt (AEMeasurable.fst g_mble) measurable_snd.aemeasurable).compl

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable;
a version for the region together with the graph of the lower function. -/
lemma nullMeasurableSet_region_between_co (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × ℝ | f p.fst ≤ p.snd} (μ.prod volume)
    rw [show {p : α × ℝ | f p.fst ≤ p.snd} = {p : α × ℝ | p.snd < f p.fst}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst f_mble)).compl
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst g_mble)

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable;
a version for the region together with the graphs of both functions. -/
lemma nullMeasurableSet_region_between_cc (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × ℝ | f p.fst ≤ p.snd} (μ.prod volume)
    rw [show {p : α × ℝ | f p.fst ≤ p.snd} = {p : α × ℝ | p.snd < f p.fst}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst f_mble)).compl
  · change NullMeasurableSet {p : α × ℝ | p.snd ≤ g p.fst} (μ.prod volume)
    rw [show {p : α × ℝ | p.snd ≤ g p.fst} = {p : α × ℝ | g p.fst < p.snd}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt (AEMeasurable.fst g_mble) measurable_snd.aemeasurable).compl

end regionBetween

/-- Consider a real set `s`. If a property is true almost everywhere in `s ∩ (a, b)` for
all `a, b ∈ s`, then it is true almost everywhere in `s`. Formulated with `μ.restrict`.
See also `ae_of_mem_of_ae_of_mem_inter_Ioo`. -/
theorem ae_restrict_of_ae_restrict_inter_Ioo {μ : Measure ℝ} [NoAtoms μ] {s : Set ℝ} {p : ℝ → Prop}
    (h : ∀ a b, a ∈ s → b ∈ s → a < b → ∀ᵐ x ∂μ.restrict (s ∩ Ioo a b), p x) :
    ∀ᵐ x ∂μ.restrict s, p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s → Set ℝ := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    ∃ A : Set (↥s × ↥s), A.Countable ∧ ⋃ i ∈ A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have : s ⊆ s \ u ∪ ⋃ p ∈ A, s ∩ T p := by
    intro x hx
    by_cases h'x : x ∈ ⋃ i : ↥s × ↥s, T i
    · rw [← hA] at h'x
      obtain ⟨p, pA, xp⟩ : ∃ p : ↥s × ↥s, p ∈ A ∧ x ∈ T p := by
        simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using h'x
      right
      exact mem_biUnion pA ⟨hx, xp⟩
    · exact Or.inl ⟨hx, h'x⟩
  apply ae_restrict_of_ae_restrict_of_subset this
  rw [ae_restrict_union_iff, ae_restrict_biUnion_iff _ A_count]
  constructor
  · have : μ.restrict (s \ u) = 0 := by simp only [restrict_eq_zero, hfinite.measure_zero]
    simp only [this, ae_zero, eventually_bot]
  · rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    dsimp [T]
    rcases le_or_lt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, restrict_empty, ae_zero, eventually_bot]
    · exact h a b as bs hab
#align ae_restrict_of_ae_restrict_inter_Ioo ae_restrict_of_ae_restrict_inter_Ioo

/-- Consider a real set `s`. If a property is true almost everywhere in `s ∩ (a, b)` for
all `a, b ∈ s`, then it is true almost everywhere in `s`. Formulated with bare membership.
See also `ae_restrict_of_ae_restrict_inter_Ioo`. -/
theorem ae_of_mem_of_ae_of_mem_inter_Ioo {μ : Measure ℝ} [NoAtoms μ] {s : Set ℝ} {p : ℝ → Prop}
    (h : ∀ a b, a ∈ s → b ∈ s → a < b → ∀ᵐ x ∂μ, x ∈ s ∩ Ioo a b → p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s → Set ℝ := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    ∃ A : Set (↥s × ↥s), A.Countable ∧ ⋃ i ∈ A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have M : ∀ᵐ x ∂μ, x ∉ s \ u := hfinite.countable.ae_not_mem _
  have M' : ∀ᵐ x ∂μ, ∀ (i : ↥s × ↥s), i ∈ A → x ∈ s ∩ T i → p x := by
    rw [ae_ball_iff A_count]
    rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    change ∀ᵐ x : ℝ ∂μ, x ∈ s ∩ Ioo a b → p x
    rcases le_or_lt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, IsEmpty.forall_iff, eventually_true,
        mem_empty_iff_false]
    · exact h a b as bs hab
  filter_upwards [M, M'] with x hx h'x
  intro xs
  by_cases Hx : x ∈ ⋃ i : ↥s × ↥s, T i
  · rw [← hA] at Hx
    obtain ⟨p, pA, xp⟩ : ∃ p : ↥s × ↥s, p ∈ A ∧ x ∈ T p := by
      simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using Hx
    apply h'x p pA ⟨xs, xp⟩
  · exact False.elim (hx ⟨xs, Hx⟩)
#align ae_of_mem_of_ae_of_mem_inter_Ioo ae_of_mem_of_ae_of_mem_inter_Ioo
