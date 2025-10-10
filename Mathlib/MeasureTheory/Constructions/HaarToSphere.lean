/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Field.Pointwise
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Generalized polar coordinate change

Consider an `n`-dimensional normed space `E` and an additive Haar measure `μ` on `E`.
Then `μ.toSphere` is the measure on the unit sphere
such that `μ.toSphere s` equals `n • μ (Set.Ioo 0 1 • s)`.

If `n ≠ 0`, then `μ` can be represented (up to `homeomorphUnitSphereProd`)
as the product of `μ.toSphere`
and the Lebesgue measure on `(0, +∞)` taken with density `fun r ↦ r ^ n`.

One can think about this fact as a version of polar coordinate change formula
for a general nontrivial normed space.
-/

open Set Function Metric MeasurableSpace intervalIntegral
open scoped Pointwise ENNReal NNReal

local notation "dim" => Module.finrank ℝ

noncomputable section
namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

namespace Measure

/-- If `μ` is an additive Haar measure on a normed space `E`,
then `μ.toSphere` is the measure on the unit sphere in `E`
such that `μ.toSphere s = Module.finrank ℝ E • μ (Set.Ioo (0 : ℝ) 1 • s)`. -/
def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

variable (μ : Measure E)

theorem toSphere_apply_aux (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : ℝ)) :
    μ ((↑) '' (homeomorphUnitSphereProd E ⁻¹' s ×ˢ Iio r)) = μ (Ioo (0 : ℝ) r • ((↑) '' s)) := by
  rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm, image_image,
    ← image_subtype_val_Ioi_Iio, image2_image_left, image2_swap, ← image_prod]
  rfl

variable [BorelSpace E]

theorem toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  rw [toSphere, smul_apply, fst_apply hs, restrict_apply (measurable_fst hs),
    ((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply,
    image_comp, Homeomorph.image_symm, univ_prod, ← Set.prod_eq, nsmul_eq_mul, toSphere_apply_aux]

theorem toSphere_apply_univ' : μ.toSphere univ = dim E * μ (ball 0 1 \ {0}) := by
  rw [μ.toSphere_apply' .univ, image_univ, Subtype.range_coe, Ioo_smul_sphere_zero] <;> simp

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

@[simp]
theorem toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1) := by
  nontriviality E
  rw [toSphere_apply_univ', measure_diff_null (measure_singleton _)]

@[simp]
theorem toSphere_real_apply_univ : μ.toSphere.real univ = dim E * μ.real (ball 0 1) := by
  simp [measureReal_def]

theorem toSphere_eq_zero_iff_finrank : μ.toSphere = 0 ↔ dim E = 0 := by
  rw [← measure_univ_eq_zero, toSphere_apply_univ]
  simp [IsOpen.measure_ne_zero]

theorem toSphere_eq_zero_iff : μ.toSphere = 0 ↔ Subsingleton E :=
  μ.toSphere_eq_zero_iff_finrank.trans Module.finrank_zero_iff

@[simp]
theorem toSphere_ne_zero [Nontrivial E] : μ.toSphere ≠ 0 := by
  simp [toSphere_eq_zero_iff, not_subsingleton]

instance : IsFiniteMeasure μ.toSphere where
  measure_univ_lt_top := by
    rw [toSphere_apply_univ']
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) <|
      measure_ball_lt_top.trans_le' <| measure_mono diff_subset

/-- The measure on `(0, +∞)` that has density `(· ^ n)` with respect to the Lebesgue measure. -/
def volumeIoiPow (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  .withDensity (.comap Subtype.val volume) fun r ↦ .ofReal (r.1 ^ n)

lemma volumeIoiPow_apply_Iio (n : ℕ) (x : Ioi (0 : ℝ)) :
    volumeIoiPow n (Iio x) = ENNReal.ofReal (x.1 ^ (n + 1) / (n + 1)) := by
  have hr₀ : 0 ≤ x.1 := le_of_lt x.2
  rw [volumeIoiPow, withDensity_apply _ measurableSet_Iio,
    setLIntegral_subtype measurableSet_Ioi _ fun a : ℝ ↦ .ofReal (a ^ n),
    image_subtype_val_Ioi_Iio, restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow _).1, ← integral_of_le hr₀]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact pow_nonneg hy.1.le _

/-- The intervals `(0, k + 1)` have finite measure `MeasureTheory.Measure.volumeIoiPow _`
and cover the whole open ray `(0, +∞)`. -/
def finiteSpanningSetsIn_volumeIoiPow_range_Iio (n : ℕ) :
    FiniteSpanningSetsIn (volumeIoiPow n) (range Iio) where
  set k := Iio ⟨k + 1, mem_Ioi.2 k.cast_add_one_pos⟩
  set_mem _ := mem_range_self _
  finite k := by simp [volumeIoiPow_apply_Iio]
  spanning := iUnion_eq_univ_iff.2 fun x ↦ ⟨⌊x.1⌋₊, Nat.lt_floor_add_one x.1⟩

instance (n : ℕ) : SigmaFinite (volumeIoiPow n) :=
  (finiteSpanningSetsIn_volumeIoiPow_range_Iio n).sigmaFinite

/-- The homeomorphism `homeomorphUnitSphereProd E` sends an additive Haar measure `μ`
to the product of `μ.toSphere` and `MeasureTheory.Measure.volumeIoiPow (dim E - 1)`,
where `dim E = Module.finrank ℝ E` is the dimension of `E`. -/
theorem measurePreserving_homeomorphUnitSphereProd :
    MeasurePreserving (homeomorphUnitSphereProd E) (μ.comap (↑))
      (μ.toSphere.prod (volumeIoiPow (dim E - 1))) := by
  nontriviality E
  refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio
    μ.toSphere.toFiniteSpanningSetsIn (finiteSpanningSetsIn_volumeIoiPow_range_Iio _)
    fun s hs ↦ forall_mem_range.2 fun r ↦ ?_
  have : Ioo (0 : ℝ) r = r.1 • Ioo (0 : ℝ) 1 := by simp [LinearOrderedField.smul_Ioo r.2.out]
  have hpos : 0 < dim E := Module.finrank_pos
  rw [(Homeomorph.measurableEmbedding _).map_apply, toSphere_apply' _ hs, volumeIoiPow_apply_Iio,
    comap_subtype_coe_apply (measurableSet_singleton _).compl, toSphere_apply_aux, this,
    smul_assoc, μ.addHaar_smul_of_nonneg r.2.out.le, Nat.sub_add_cancel hpos, Nat.cast_pred hpos,
    sub_add_cancel, mul_right_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul, mul_div_cancel₀]
  exacts [(Nat.cast_pos.2 hpos).ne', Nat.cast_nonneg _]

end Measure

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Nontrivial E] (μ : Measure E) [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

lemma integrable_fun_norm_addHaar {f : ℝ → F} :
    Integrable (f ‖·‖) μ ↔ IntegrableOn (fun y : ℝ ↦ y ^ (dim E - 1) • f y) (Ioi 0) := by
  have := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb (g := f ∘ (↑) ∘ Prod.snd)
    (Homeomorph.measurableEmbedding _)
  simp only [comp_def, homeomorphUnitSphereProd_apply_snd_coe] at this
  rw [← restrict_compl_singleton (μ := μ) 0, ← IntegrableOn,
    integrableOn_iff_comap_subtypeVal (by measurability), comp_def, this,
    Integrable.comp_snd_iff (β := Ioi 0) (f := (f <| Subtype.val ·)),
    integrableOn_iff_comap_subtypeVal, comp_def, Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul', integrable_congr]
  · refine .of_forall ?_
    rintro ⟨x, hx : 0 < x⟩
    simp (disch := positivity) [ENNReal.toReal_ofReal]
  · fun_prop
  · simp
  · measurability
  · simp

lemma integral_fun_norm_addHaar (f : ℝ → F) :
    ∫ x, f (‖x‖) ∂μ = dim E • μ.real (ball 0 1) • ∫ y in Ioi (0 : ℝ), y ^ (dim E - 1) • f y :=
  calc
    ∫ x, f (‖x‖) ∂μ = ∫ x : ({(0)}ᶜ : Set E), f (‖x.1‖) ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ f (‖x‖),
        restrict_compl_singleton]
    _ = ∫ x : sphere (0 : E) 1 × Ioi (0 : ℝ), f x.2 ∂μ.toSphere.prod (.volumeIoiPow (dim E - 1)) :=
      μ.measurePreserving_homeomorphUnitSphereProd.integral_comp (Homeomorph.measurableEmbedding _)
        (f ∘ Subtype.val ∘ Prod.snd)
    _ = μ.toSphere.real univ • ∫ x : Ioi (0 : ℝ), f x ∂.volumeIoiPow (dim E - 1) :=
      integral_fun_snd (f ∘ Subtype.val)
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul, μ.toSphere_real_apply_univ,
        ← nsmul_eq_mul, smul_assoc,
        integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ (dim E - 1)) • f a,
        setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
      · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end MeasureTheory
