/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

In this file we provide a way to rewrite integrals and integrability
of functions that depend on the norm only in terms of integral over `(0, +∞)`.
We also provide a positive lower estimate on the `(Measure.toSphere μ)`-measure
of a ball of radius `ε > 0` on the unit sphere.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

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

instance toSphere.instIsOpenPosMeasure [FiniteDimensional ℝ E] [μ.IsOpenPosMeasure] :
    μ.toSphere.IsOpenPosMeasure where
  open_pos := by
    nontriviality E using not_nonempty_iff_eq_empty
    rintro U hUo hU
    rw [μ.toSphere_apply' hUo.measurableSet]
    apply mul_ne_zero (by simp [Module.finrank_pos.ne'])
    exact isOpen_Ioo.smul_sphere one_ne_zero (by simp) hUo |>.measure_ne_zero _ (by simpa)

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

/-- An auxiliary lemma for `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball`.
The estimate in this lemma is highly suboptimal.
For a non-private lemma, we should aim for a more precise and a more general fact
(e.g., an estimate on the radius of a ball centered at `t • x`
that is guaranteed to be a subset of the cone. -/
private lemma ball_subset_sector_of_small_epsilon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : ‖x‖ = 1) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    ball ((1 - ε / 4) • x) (ε / 4) ⊆
      Ioo (0 : ℝ) 1 • (ball x ε ∩ sphere (0 : E) 1) := by
  intro y hy
  rw [mem_ball] at hy
  have habs : |1 - ε / 4| = 1 - ε / 4 := abs_of_nonneg (by linarith)
  -- Note that $y ≠ 0$.
  have hy₀ : y ≠ 0 := by
    rintro rfl
    have : 1 - ε / 4 < ε / 4 := by simpa [norm_smul, habs, hx] using hy
    linarith
  have hy₁ : ‖y‖ < 1 := calc
    ‖y‖ ≤ dist y ((1 - ε / 4) • x) + ‖(1 - ε / 4) • x‖ := by
      simpa using dist_triangle y ((1 - ε / 4) • x) 0
    _ < ε / 4 + ‖(1 - ε / 4) • x‖ := by gcongr
    _ = 1 := by simp [norm_smul, habs, hx]
  -- Let $u = y / \|y\|$. We show $\|u - x\| < \epsilon$.
  set u : E := ‖y‖⁻¹ • y
  have hu₁ : ‖u‖ = 1 := by simp [u, hy₀, norm_smul]
  refine ⟨‖y‖, ⟨by simpa, hy₁⟩, u, ⟨?_, by simpa⟩, by simp [u, hy₀]⟩
  rw [mem_ball]
  have hyx := calc
    dist y x ≤ dist y ((1 - ε / 4) • x) + dist ((1 - ε / 4) • x) x := dist_triangle ..
    _ < ε / 4 + dist ((1 - ε / 4) • x) x := by gcongr
    _ = ε / 4 + ε / 4 := by simp [sub_smul, norm_smul, hx, abs_of_pos hε]
    _ = ε / 2 := by ring
  have huy : dist u y ≤ dist x y := by
    have H : u - y = (1 - ‖y‖) • u := by simp [u, hy₀, sub_smul]
    simpa [dist_eq_norm_sub, H, norm_smul, abs_of_nonneg, hy₁.le, hu₁, hx]
      using dist_triangle x y 0
  linarith [dist_triangle u y x, dist_comm x y]

/-- Lower estimate on the measure of the `ε`-cone in an `n`-dimensional normed space
divided by the measure of the ball. -/
@[irreducible]
noncomputable def toSphereBallBound (n : ℕ) (ε : ℝ) : ℝ≥0 :=
  if n ≠ 0 ∧ 0 < ε then n * ((min (Real.toNNReal ε) 2) / 4) ^ n else 1

set_option backward.isDefEq.respectTransparency false in
theorem toSphereBallBound_pos (n : ℕ) (ε : ℝ) : 0 < toSphereBallBound n ε := by
  unfold toSphereBallBound
  split_ifs with h
  · cases h
    positivity
  · positivity

/-- A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension and `ε`,
which is positive for positive `n` and `ε`. -/
theorem toSphereBallBound_mul_measure_unitBall_le_toSphere_ball {ε : ℝ}
    (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank ℝ E) ε * μ (ball 0 1) ≤ μ.toSphere (ball x ε) := by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne Norm.norm (by simp)⟩⟩
  wlog hε₂ : ε ≤ 2 generalizing ε
  · trans μ.toSphere (ball x (min ε 2))
    · simpa [Real.toNNReal_monotone.map_min, toSphereBallBound]
        using this (ε := min ε 2) (by simp [hε]) (by simp)
    · gcongr
      simp
  rw [μ.toSphere_apply' measurableSet_ball, Subtype.image_ball, setOf_mem_eq]
  grw [← ball_subset_sector_of_small_epsilon] <;> try assumption
  · have hdim : Module.finrank ℝ E ≠ 0 := Module.finrank_pos.ne'
    have : min (ENNReal.ofReal ε) 2 = ENNReal.ofReal ε := by simpa
    simp (disch := positivity) [μ.addHaar_ball_of_pos (r := ε / 4), ENNReal.ofReal_div_of_pos,
      toSphereBallBound, mul_assoc, ENNReal.ofNNReal_toNNReal, this, hdim, hε]
  · simp

/-- A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension and `ε`,
which is positive for positive `n` and `ε`.

This is a version stated in terms `MeasureTheory.Measure.real`. -/
theorem toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    {ε : ℝ} (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank ℝ E) ε * μ.real (ball 0 1) ≤
      μ.toSphere.real (ball x ε) := by
  grw [Measure.real, Measure.real, ← toSphereBallBound_mul_measure_unitBall_le_toSphere_ball μ hε,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp

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
    _ = ∫ x, f x.2 ∂μ.toSphere.prod (.volumeIoiPow (dim E - 1)) := by
      simpa using μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ Prod.snd)
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
