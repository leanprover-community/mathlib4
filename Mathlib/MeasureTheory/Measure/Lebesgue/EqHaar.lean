/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Doubling

#align_import measure_theory.measure.lebesgue.eq_haar from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`MeasureTheory.addHaarMeasure_eq_volume` and `MeasureTheory.addHaarMeasure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linearMap_addHaar_eq_smul_addHaar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `addHaar_preimage_linearMap` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `addHaar_image_linearMap` : when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `addHaar_submodule` : a strict submodule has measure `0`.
* `addHaar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `addHaar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_closedBall`: the measure of `closedBall x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_sphere`: spheres have zero measure.

This makes it possible to associate a Lebesgue measure to an `n`-alternating map in dimension `n`.
This measure is called `AlternatingMap.measure`. Its main property is
`ω.measure_parallelepiped v`, stating that the associated measure of the parallelepiped spanned
by vectors `v₁, ..., vₙ` is given by `|ω v|`.

We also show that a Lebesgue density point `x` of a set `s` (with respect to closed balls) has
density one for the rescaled copies `{x} + r • t` of a given set `t` with positive measure, in
`tendsto_addHaar_inter_smul_one_of_density_one`. In particular, `s` intersects `{x} + r • t` for
small `r`, see `eventually_nonempty_inter_smul_of_density_one`.
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

assert_not_exists MeasureTheory.integral

open TopologicalSpace Set Filter Metric

open scoped ENNReal Pointwise Topology NNReal

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.Icc01 : PositiveCompacts ℝ where
  carrier := Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]
                           -- 🎉 no goals
#align topological_space.positive_compacts.Icc01 TopologicalSpace.PositiveCompacts.Icc01

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type*) [Fintype ι] :
    PositiveCompacts (ι → ℝ) where
  carrier := pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]
#align topological_space.positive_compacts.pi_Icc01 TopologicalSpace.PositiveCompacts.piIcc01

/-- The parallelepiped formed from the standard basis for `ι → ℝ` is `[0,1]^ι` -/
theorem Basis.parallelepiped_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).parallelepiped = TopologicalSpace.PositiveCompacts.piIcc01 ι :=
  SetLike.coe_injective <| by
    refine' Eq.trans _ ((uIcc_of_le _).trans (Set.pi_univ_Icc _ _).symm)
    -- ⊢ ↑(parallelepiped (Pi.basisFun ℝ ι)) = uIcc (fun i => 0) fun i => 1
    · classical convert parallelepiped_single (ι := ι) 1
      -- 🎉 no goals
    · exact zero_le_one
      -- 🎉 no goals
#align basis.parallelepiped_basis_fun Basis.parallelepiped_basisFun

namespace MeasureTheory

open Measure TopologicalSpace.PositiveCompacts FiniteDimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
theorem addHaarMeasure_eq_volume : addHaarMeasure Icc01 = volume := by
  convert (addHaarMeasure_unique volume Icc01).symm; simp [Icc01]
  -- ⊢ addHaarMeasure Icc01 = ↑↑volume ↑Icc01 • addHaarMeasure Icc01
                                                     -- 🎉 no goals
#align measure_theory.add_haar_measure_eq_volume MeasureTheory.addHaarMeasure_eq_volume

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
theorem addHaarMeasure_eq_volume_pi (ι : Type*) [Fintype ι] :
    addHaarMeasure (piIcc01 ι) = volume := by
  convert (addHaarMeasure_unique volume (piIcc01 ι)).symm
  -- ⊢ addHaarMeasure (piIcc01 ι) = ↑↑volume ↑(piIcc01 ι) • addHaarMeasure (piIcc01 …
  simp only [piIcc01, volume_pi_pi fun _ => Icc (0 : ℝ) 1, PositiveCompacts.coe_mk,
    Compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]
#align measure_theory.add_haar_measure_eq_volume_pi MeasureTheory.addHaarMeasure_eq_volume_pi

-- porting note: TODO: remove this instance?
instance isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
  inferInstance
#align measure_theory.is_add_haar_measure_volume_pi MeasureTheory.isAddHaarMeasure_volume_pi

namespace Measure

/-!
### Strict subspaces have zero measure
-/


/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bounded. -/
theorem addHaar_eq_zero_of_disjoint_translates_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (sb : Bounded s) (hu : Bounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  by_contra h
  -- ⊢ False
  apply lt_irrefl ∞
  -- ⊢ ⊤ < ⊤
  calc
    ∞ = ∑' _ : ℕ, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : ℕ, μ ({u n} + s) := by
      congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
    _ = μ (⋃ n, {u n} + s) := Eq.symm <| measure_iUnion hs fun n => by
      simpa only [image_add_left, singleton_add] using measurable_id.const_add _ h's
    _ = μ (range u + s) := by rw [← iUnion_add, iUnion_singleton_eq_range]
    _ < ∞ := Bounded.measure_lt_top (hu.add sb)
#align measure_theory.measure.add_haar_eq_zero_of_disjoint_translates_aux MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates_aux

/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. -/
theorem addHaar_eq_zero_of_disjoint_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (hu : Bounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  suffices H : ∀ R, μ (s ∩ closedBall 0 R) = 0
  -- ⊢ ↑↑μ s = 0
  · apply le_antisymm _ (zero_le _)
    -- ⊢ ↑↑μ s ≤ 0
    calc
      μ s ≤ ∑' n : ℕ, μ (s ∩ closedBall 0 n) := by
        conv_lhs => rw [← iUnion_inter_closedBall_nat s 0]
        exact measure_iUnion_le _
      _ = 0 := by simp only [H, tsum_zero]
  intro R
  -- ⊢ ↑↑μ (s ∩ closedBall 0 R) = 0
  apply addHaar_eq_zero_of_disjoint_translates_aux μ u
    (bounded_closedBall.mono (inter_subset_right _ _)) hu _ (h's.inter measurableSet_closedBall)
  refine pairwise_disjoint_mono hs fun n => ?_
  -- ⊢ {u n} + s ∩ closedBall 0 R ≤ {u n} + s
  exact add_subset_add Subset.rfl (inter_subset_left _ _)
  -- 🎉 no goals
#align measure_theory.measure.add_haar_eq_zero_of_disjoint_translates MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates

/-- A strict vector subspace has measure zero. -/
theorem addHaar_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (s : Submodule ℝ E)
    (hs : s ≠ ⊤) : μ s = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne.def, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  -- ⊢ ↑↑μ ↑s = 0
  have A : Bounded (range fun n : ℕ => c ^ n • x) :=
    haveI : Tendsto (fun n : ℕ => c ^ n • x) atTop (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_atTop_nhds_0_of_lt_1 cpos.le cone).smul_const x
    bounded_range_of_tendsto _ this
  apply addHaar_eq_zero_of_disjoint_translates μ _ A _
    (Submodule.closed_of_finiteDimensional s).measurableSet
  intro m n hmn
  -- ⊢ (Disjoint on fun n => {c ^ n • x} + ↑s) m n
  simp only [Function.onFun, image_add_left, singleton_add, disjoint_left, mem_preimage,
    SetLike.mem_coe]
  intro y hym hyn
  -- ⊢ False
  have A : (c ^ n - c ^ m) • x ∈ s := by
    convert s.sub_mem hym hyn using 1
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m ≠ 0 := by
    simpa only [sub_eq_zero, Ne.def] using (strictAnti_pow cpos cone).injective.ne hmn.symm
  have : x ∈ s := by
    convert s.smul_mem (c ^ n - c ^ m)⁻¹ A
    rw [smul_smul, inv_mul_cancel H, one_smul]
  exact hx this
  -- 🎉 no goals
#align measure_theory.measure.add_haar_submodule MeasureTheory.Measure.addHaar_submodule

/-- A strict affine subspace has measure zero. -/
theorem addHaar_affineSubspace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) : μ s = 0 := by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  -- ⊢ ↑↑μ ↑⊥ = 0
  · rw [AffineSubspace.bot_coe, measure_empty]
    -- 🎉 no goals
  rw [Ne.def, ← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  -- ⊢ ↑↑μ ↑s = 0
  rcases hne with ⟨x, hx : x ∈ s⟩
  -- ⊢ ↑↑μ ↑s = 0
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg,
    image_add_right, neg_neg, measure_preimage_add_right] using addHaar_submodule μ s.direction hs
#align measure_theory.measure.add_haar_affine_subspace MeasureTheory.Measure.addHaar_affineSubspace

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/

theorem map_linearMap_addHaar_pi_eq_smul_addHaar {ι : Type*} [Finite ι] {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ}
    (hf : LinearMap.det f ≠ 0) (μ : Measure (ι → ℝ)) [IsAddHaarMeasure μ] :
    Measure.map f μ = ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • μ := by
  cases nonempty_fintype ι
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := addHaarMeasure_unique μ (piIcc01 ι)
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  rw [this, addHaarMeasure_eq_volume_pi, Measure.map_smul,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hf, smul_comm]
#align measure_theory.measure.map_linear_map_add_haar_pi_eq_smul_add_haar MeasureTheory.Measure.map_linearMap_addHaar_pi_eq_smul_addHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

theorem map_linearMap_addHaar_eq_smul_addHaar {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) :
    Measure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ := by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linearMap_addHaar_pi_eq_smul_addHaar`.
  let ι := Fin (finrank ℝ E)
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  haveI : FiniteDimensional ℝ (ι → ℝ) := by infer_instance
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by simp
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  have e : E ≃ₗ[ℝ] ι → ℝ := LinearEquiv.ofFinrankEq E (ι → ℝ) this
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] ι → ℝ).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) := ⟨_, rfl⟩
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  have gdet : LinearMap.det g = LinearMap.det f := by rw [hg]; exact LinearMap.det_conj f e
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ
  rw [← gdet] at hf ⊢
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(↑LinearMap.det g)⁻¹| • μ
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] ι → ℝ)) := by
    ext x
    simp only [LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_comp,
      LinearEquiv.symm_apply_apply, hg]
  simp only [fg, LinearEquiv.coe_coe, LinearMap.coe_comp]
  -- ⊢ map (↑(LinearEquiv.symm e) ∘ ↑g ∘ ↑e) μ = ENNReal.ofReal |(↑LinearMap.det g) …
  have Ce : Continuous e := (e : E →ₗ[ℝ] ι → ℝ).continuous_of_finiteDimensional
  -- ⊢ map (↑(LinearEquiv.symm e) ∘ ↑g ∘ ↑e) μ = ENNReal.ofReal |(↑LinearMap.det g) …
  have Cg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  -- ⊢ map (↑(LinearEquiv.symm e) ∘ ↑g ∘ ↑e) μ = ENNReal.ofReal |(↑LinearMap.det g) …
  have Cesymm : Continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finiteDimensional
  -- ⊢ map (↑(LinearEquiv.symm e) ∘ ↑g ∘ ↑e) μ = ENNReal.ofReal |(↑LinearMap.det g) …
  rw [← map_map Cesymm.measurable (Cg.comp Ce).measurable, ← map_map Cg.measurable Ce.measurable]
  -- ⊢ map (↑(LinearEquiv.symm e)) (map (↑g) (map (↑e) μ)) = ENNReal.ofReal |(↑Line …
  haveI : IsAddHaarMeasure (map e μ) := (e : E ≃+ (ι → ℝ)).isAddHaarMeasure_map μ Ce Cesymm
  -- ⊢ map (↑(LinearEquiv.symm e)) (map (↑g) (map (↑e) μ)) = ENNReal.ofReal |(↑Line …
  have ecomp : e.symm ∘ e = id := by
    ext x; simp only [id.def, Function.comp_apply, LinearEquiv.symm_apply_apply]
  rw [map_linearMap_addHaar_pi_eq_smul_addHaar hf (map e μ), Measure.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, Measure.map_id]
#align measure_theory.measure.map_linear_map_add_haar_eq_smul_add_haar MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem addHaar_preimage_linearMap {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s :=
  calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply
          s).symm
    _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s := by
      rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]; rfl
      -- ⊢ ↑↑(ENNReal.ofReal |(↑LinearMap.det f)⁻¹| • μ) s = ENNReal.ofReal |(↑LinearMa …
                                                       -- 🎉 no goals
#align measure_theory.measure.add_haar_preimage_linear_map MeasureTheory.Measure.addHaar_preimage_linearMap

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem addHaar_preimage_continuousLinearMap {f : E →L[ℝ] E}
    (hf : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs (LinearMap.det (f : E →ₗ[ℝ] E))⁻¹) * μ s :=
  addHaar_preimage_linearMap μ hf s
#align measure_theory.measure.add_haar_preimage_continuous_linear_map MeasureTheory.Measure.addHaar_preimage_continuousLinearMap

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem addHaar_preimage_linearEquiv (f : E ≃ₗ[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E →ₗ[ℝ] E)| * μ s := by
  have A : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  -- ⊢ ↑↑μ (↑f ⁻¹' s) = ENNReal.ofReal |↑LinearMap.det ↑(LinearEquiv.symm f)| * ↑↑μ s
  convert addHaar_preimage_linearMap μ A s
  -- ⊢ ↑LinearMap.det ↑(LinearEquiv.symm f) = (↑LinearMap.det ↑f)⁻¹
  simp only [LinearEquiv.det_coe_symm]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_preimage_linear_equiv MeasureTheory.Measure.addHaar_preimage_linearEquiv

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem addHaar_preimage_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E →ₗ[ℝ] E)| * μ s :=
  addHaar_preimage_linearEquiv μ _ s
#align measure_theory.measure.add_haar_preimage_continuous_linear_equiv MeasureTheory.Measure.addHaar_preimage_continuousLinearEquiv

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem addHaar_image_linearMap (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s := by
  rcases ne_or_eq (LinearMap.det f) 0 with (hf | hf)
  -- ⊢ ↑↑μ (↑f '' s) = ENNReal.ofReal |↑LinearMap.det f| * ↑↑μ s
  · let g := (f.equivOfDetNeZero hf).toContinuousLinearEquiv
    -- ⊢ ↑↑μ (↑f '' s) = ENNReal.ofReal |↑LinearMap.det f| * ↑↑μ s
    change μ (g '' s) = _
    -- ⊢ ↑↑μ (↑g '' s) = ENNReal.ofReal |↑LinearMap.det f| * ↑↑μ s
    rw [ContinuousLinearEquiv.image_eq_preimage g s, addHaar_preimage_continuousLinearEquiv]
    -- ⊢ ENNReal.ofReal |↑LinearMap.det ↑↑(ContinuousLinearEquiv.symm (ContinuousLine …
    congr
    -- 🎉 no goals
  · simp only [hf, zero_mul, ENNReal.ofReal_zero, abs_zero]
    -- ⊢ ↑↑μ ((fun a => ↑f a) '' s) = 0
    have : μ (LinearMap.range f) = 0 :=
      addHaar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).ne
    exact le_antisymm (le_trans (measure_mono (image_subset_range _ _)) this.le) (zero_le _)
    -- 🎉 no goals
#align measure_theory.measure.add_haar_image_linear_map MeasureTheory.Measure.addHaar_image_linearMap

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem addHaar_image_continuousLinearMap (f : E →L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E →ₗ[ℝ] E)| * μ s :=
  addHaar_image_linearMap μ _ s
#align measure_theory.measure.add_haar_image_continuous_linear_map MeasureTheory.Measure.addHaar_image_continuousLinearMap

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem addHaar_image_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E →ₗ[ℝ] E)| * μ s :=
  μ.addHaar_image_linearMap (f : E →ₗ[ℝ] E) s
#align measure_theory.measure.add_haar_image_continuous_linear_equiv MeasureTheory.Measure.addHaar_image_continuousLinearEquiv

/-!
### Basic properties of Haar measures on real vector spaces
-/


theorem map_addHaar_smul {r : ℝ} (hr : r ≠ 0) :
    Measure.map ((· • ·) r) μ = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) • μ := by
  let f : E →ₗ[ℝ] E := r • (1 : E →ₗ[ℝ] E)
  -- ⊢ map ((fun x x_1 => x • x_1) r) μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| • μ
  change Measure.map f μ = _
  -- ⊢ map (↑f) μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| • μ
  have hf : LinearMap.det f ≠ 0 := by
    simp only [mul_one, LinearMap.det_smul, Ne.def, MonoidHom.map_one]
    intro h
    exact hr (pow_eq_zero h)
  simp only [map_linearMap_addHaar_eq_smul_addHaar μ hf, mul_one, LinearMap.det_smul, map_one]
  -- 🎉 no goals
#align measure_theory.measure.map_add_haar_smul MeasureTheory.Measure.map_addHaar_smul

@[simp]
theorem addHaar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    μ ((· • ·) r ⁻¹' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s :=
  calc
    μ ((· • ·) r ⁻¹' s) = Measure.map ((· • ·) r) μ s :=
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s := by
      rw [map_addHaar_smul μ hr, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
        smul_eq_mul]
#align measure_theory.measure.add_haar_preimage_smul MeasureTheory.Measure.addHaar_preimage_smul

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp]
theorem addHaar_smul (r : ℝ) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  -- ⊢ ↑↑μ (r • s) = ENNReal.ofReal |r ^ finrank ℝ E| * ↑↑μ s
  · rw [← preimage_smul_inv₀ h, addHaar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
    -- 🎉 no goals
  rcases eq_empty_or_nonempty s with (rfl | hs)
  -- ⊢ ↑↑μ (0 • ∅) = ENNReal.ofReal |0 ^ finrank ℝ E| * ↑↑μ ∅
  · simp only [measure_empty, mul_zero, smul_set_empty]
    -- 🎉 no goals
  rw [zero_smul_set hs, ← singleton_zero]
  -- ⊢ ↑↑μ {0} = ENNReal.ofReal |0 ^ finrank ℝ E| * ↑↑μ s
  by_cases h : finrank ℝ E = 0
  -- ⊢ ↑↑μ {0} = ENNReal.ofReal |0 ^ finrank ℝ E| * ↑↑μ s
  · haveI : Subsingleton E := finrank_zero_iff.1 h
    -- ⊢ ↑↑μ {0} = ENNReal.ofReal |0 ^ finrank ℝ E| * ↑↑μ s
    simp only [h, one_mul, ENNReal.ofReal_one, abs_one, Subsingleton.eq_univ_of_nonempty hs,
      pow_zero, Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
  · haveI : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    -- ⊢ ↑↑μ {0} = ENNReal.ofReal |0 ^ finrank ℝ E| * ↑↑μ s
    simp only [h, zero_mul, ENNReal.ofReal_zero, abs_zero, Ne.def, not_false_iff,
      zero_pow', measure_singleton]
#align measure_theory.measure.add_haar_smul MeasureTheory.Measure.addHaar_smul

theorem addHaar_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (r ^ finrank ℝ E) * μ s := by
  rw [addHaar_smul, abs_pow, abs_of_nonneg hr]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_smul_of_nonneg MeasureTheory.Measure.addHaar_smul_of_nonneg

variable {μ} {s : Set E}

-- Note: We might want to rename this once we acquire the lemma corresponding to
-- `MeasurableSet.const_smul`
theorem NullMeasurableSet.const_smul (hs : NullMeasurableSet s μ) (r : ℝ) :
    NullMeasurableSet (r • s) μ := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  -- ⊢ NullMeasurableSet (r • ∅)
  · simp
    -- 🎉 no goals
  obtain rfl | hr := eq_or_ne r 0
  -- ⊢ NullMeasurableSet (0 • s)
  · simpa [zero_smul_set hs'] using nullMeasurableSet_singleton _
    -- 🎉 no goals
  obtain ⟨t, ht, hst⟩ := hs
  -- ⊢ NullMeasurableSet (r • s)
  refine' ⟨_, ht.const_smul_of_ne_zero hr, _⟩
  -- ⊢ r • s =ᶠ[ae μ] r • t
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  -- ⊢ ↑↑μ ((r • s) ∆ (r • t)) = 0
  rw [← smul_set_symmDiff₀ hr, addHaar_smul μ, hst, mul_zero]
  -- 🎉 no goals
#align measure_theory.measure.null_measurable_set.const_smul MeasureTheory.Measure.NullMeasurableSet.const_smul

variable (μ)

@[simp]
theorem addHaar_image_homothety (x : E) (r : ℝ) (s : Set E) :
    μ (AffineMap.homothety x r '' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s :=
  calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]; rfl
      -- ⊢ ↑↑μ ((fun a => ↑(AffineMap.homothety x r) a) '' s) = ↑↑μ ((fun x_1 => r • (x …
                                                               -- 🎉 no goals
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, addHaar_smul]
      -- 🎉 no goals
#align measure_theory.measure.add_haar_image_homothety MeasureTheory.Measure.addHaar_image_homothety

/-! We don't need to state `map_addHaar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/

theorem addHaar_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) : μ (ball x r) = μ (ball (0 : E) r) := by
  have : ball (0 : E) r = (· + ·) x ⁻¹' ball x r := by simp [preimage_add_ball]
  -- ⊢ ↑↑μ (ball x r) = ↑↑μ (ball 0 r)
  rw [this, measure_preimage_add]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_ball_center MeasureTheory.Measure.addHaar_ball_center

theorem addHaar_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (closedBall (0 : E) r) := by
  have : closedBall (0 : E) r = (· + ·) x ⁻¹' closedBall x r := by simp [preimage_add_closedBall]
  -- ⊢ ↑↑μ (closedBall x r) = ↑↑μ (closedBall 0 r)
  rw [this, measure_preimage_add]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_ball_center MeasureTheory.Measure.addHaar_closedBall_center

theorem addHaar_ball_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) := by
  have : ball (0 : E) (r * s) = r • ball (0 : E) s := by
    simp only [_root_.smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_ball_center, abs_pow]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_ball_mul_of_pos MeasureTheory.Measure.addHaar_ball_mul_of_pos

theorem addHaar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul_of_pos μ x hr, mul_one]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_ball_of_pos MeasureTheory.Measure.addHaar_ball_of_pos

theorem addHaar_ball_mul [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) := by
  rcases hr.eq_or_lt with (rfl | h)
  -- ⊢ ↑↑μ (ball x (0 * s)) = ENNReal.ofReal (0 ^ finrank ℝ E) * ↑↑μ (ball 0 s)
  · simp only [zero_pow (finrank_pos (K := ℝ) (V := E)), measure_empty, zero_mul,
      ENNReal.ofReal_zero, ball_zero]
  · exact addHaar_ball_mul_of_pos μ x h s
    -- 🎉 no goals
#align measure_theory.measure.add_haar_ball_mul MeasureTheory.Measure.addHaar_ball_mul

theorem addHaar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul μ x hr, mul_one]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_ball MeasureTheory.Measure.addHaar_ball

theorem addHaar_closedBall_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_closedBall_center, abs_pow]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_ball_mul_of_pos MeasureTheory.Measure.addHaar_closedBall_mul_of_pos

theorem addHaar_closedBall_mul (x : E) {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (hs : 0 ≤ s) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, addHaar_smul, abs_of_nonneg hr, addHaar_closedBall_center, abs_pow]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_ball_mul MeasureTheory.Measure.addHaar_closedBall_mul

/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `addHaar_closedBall`, which uses the measure of the open unit ball as a standard
form. -/
theorem addHaar_closedBall' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 1) := by
  rw [← addHaar_closedBall_mul μ x hr zero_le_one, mul_one]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_ball' MeasureTheory.Measure.addHaar_closedBall'

theorem addHaar_closed_unit_ball_eq_addHaar_unit_ball :
    μ (closedBall (0 : E) 1) = μ (ball 0 1) := by
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  -- ⊢ ↑↑μ (closedBall 0 1) ≤ ↑↑μ (ball 0 1)
  have A : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall (0 : E) 1)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ finrank ℝ E) * μ (closedBall (0 : E) 1))) := by
    refine' ENNReal.Tendsto.mul _ (by simp) tendsto_const_nhds (by simp)
    exact ENNReal.tendsto_ofReal ((tendsto_id'.2 nhdsWithin_le_nhds).pow _)
  simp only [one_pow, one_mul, ENNReal.ofReal_one] at A
  -- ⊢ ↑↑μ (closedBall 0 1) ≤ ↑↑μ (ball 0 1)
  refine' le_of_tendsto A _
  -- ⊢ ∀ᶠ (c : ℝ) in 𝓝[Iio 1] 1, ENNReal.ofReal (c ^ finrank ℝ E) * ↑↑μ (closedBall …
  refine' mem_nhdsWithin_Iio_iff_exists_Ioo_subset.2 ⟨(0 : ℝ), by simp, fun r hr => _⟩
  -- ⊢ r ∈ {x | (fun c => ENNReal.ofReal (c ^ finrank ℝ E) * ↑↑μ (closedBall 0 1) ≤ …
  dsimp
  -- ⊢ ENNReal.ofReal (r ^ finrank ℝ E) * ↑↑μ (closedBall 0 1) ≤ ↑↑μ (ball 0 1)
  rw [← addHaar_closedBall' μ (0 : E) hr.1.le]
  -- ⊢ ↑↑μ (closedBall 0 r) ≤ ↑↑μ (ball 0 1)
  exact measure_mono (closedBall_subset_ball hr.2)
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_unit_ball_eq_add_haar_unit_ball MeasureTheory.Measure.addHaar_closed_unit_ball_eq_addHaar_unit_ball

theorem addHaar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [addHaar_closedBall' μ x hr, addHaar_closed_unit_ball_eq_addHaar_unit_ball]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_ball MeasureTheory.Measure.addHaar_closedBall

theorem addHaar_closedBall_eq_addHaar_ball [Nontrivial E] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (ball x r) := by
  by_cases h : r < 0
  -- ⊢ ↑↑μ (closedBall x r) = ↑↑μ (ball x r)
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
    -- 🎉 no goals
  push_neg at h
  -- ⊢ ↑↑μ (closedBall x r) = ↑↑μ (ball x r)
  rw [addHaar_closedBall μ x h, addHaar_ball μ x h]
  -- 🎉 no goals
#align measure_theory.measure.add_haar_closed_ball_eq_add_haar_ball MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball

theorem addHaar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (sphere x r) = 0 := by
  rcases hr.lt_or_lt with (h | h)
  -- ⊢ ↑↑μ (sphere x r) = 0
  · simp only [empty_diff, measure_empty, ← closedBall_diff_ball, closedBall_eq_empty.2 h]
    -- 🎉 no goals
  · rw [← closedBall_diff_ball,
      measure_diff ball_subset_closedBall measurableSet_ball measure_ball_lt_top.ne,
      addHaar_ball_of_pos μ _ h, addHaar_closedBall μ _ h.le, tsub_self]
#align measure_theory.measure.add_haar_sphere_of_ne_zero MeasureTheory.Measure.addHaar_sphere_of_ne_zero

theorem addHaar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  -- ⊢ ↑↑μ (sphere x 0) = 0
  · rw [sphere_zero, measure_singleton]
    -- 🎉 no goals
  · exact addHaar_sphere_of_ne_zero μ x h
    -- 🎉 no goals
#align measure_theory.measure.add_haar_sphere MeasureTheory.Measure.addHaar_sphere

theorem addHaar_singleton_add_smul_div_singleton_add_smul {r : ℝ} (hr : r ≠ 0) (x y : E)
    (s t : Set E) : μ ({x} + r • s) / μ ({y} + r • t) = μ s / μ t :=
  calc
    μ ({x} + r • s) / μ ({y} + r • t) = ENNReal.ofReal (|r| ^ finrank ℝ E) * μ s *
        (ENNReal.ofReal (|r| ^ finrank ℝ E) * μ t)⁻¹ := by
      simp only [div_eq_mul_inv, addHaar_smul, image_add_left, measure_preimage_add, abs_pow,
        singleton_add]
    _ = ENNReal.ofReal (|r| ^ finrank ℝ E) * (ENNReal.ofReal (|r| ^ finrank ℝ E))⁻¹ *
          (μ s * (μ t)⁻¹) := by
      rw [ENNReal.mul_inv]
      · ring
        -- 🎉 no goals
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne.def, true_or_iff]
        -- 🎉 no goals
      · simp only [ENNReal.ofReal_ne_top, true_or_iff, Ne.def, not_false_iff]
        -- 🎉 no goals
    _ = μ s / μ t := by
      rw [ENNReal.mul_inv_cancel, one_mul, div_eq_mul_inv]
      -- ⊢ ENNReal.ofReal (|r| ^ finrank ℝ E) ≠ 0
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne.def]
        -- 🎉 no goals
      · simp only [ENNReal.ofReal_ne_top, Ne.def, not_false_iff]
        -- 🎉 no goals
#align measure_theory.measure.add_haar_singleton_add_smul_div_singleton_add_smul MeasureTheory.Measure.addHaar_singleton_add_smul_div_singleton_add_smul

instance (priority := 100) isUnifLocDoublingMeasureOfIsAddHaarMeasure :
    IsUnifLocDoublingMeasure μ := by
  refine' ⟨⟨(2 : ℝ≥0) ^ finrank ℝ E, _⟩⟩
  -- ⊢ ∀ᶠ (ε : ℝ) in 𝓝[Ioi 0] 0, ∀ (x : E), ↑↑μ (closedBall x (2 * ε)) ≤ ↑(2 ^ finr …
  filter_upwards [self_mem_nhdsWithin] with r hr x
  -- ⊢ ↑↑μ (closedBall x (2 * r)) ≤ ↑(2 ^ finrank ℝ E) * ↑↑μ (closedBall x r)
  rw [addHaar_closedBall_mul μ x zero_le_two (le_of_lt hr), addHaar_closedBall_center μ x,
    ENNReal.ofReal, Real.toNNReal_pow zero_le_two]
  simp only [Real.toNNReal_ofNat, le_refl]
  -- 🎉 no goals
#align measure_theory.measure.is_unif_loc_doubling_measure_of_is_add_haar_measure MeasureTheory.Measure.isUnifLocDoublingMeasureOfIsAddHaarMeasure

section

/-!
### The Lebesgue measure associated to an alternating map
-/

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem addHaar_parallelepiped (b : Basis ι ℝ G) (v : ι → G) :
    b.addHaar (parallelepiped v) = ENNReal.ofReal |b.det v| := by
  have : FiniteDimensional ℝ G := FiniteDimensional.of_fintype_basis b
  -- ⊢ ↑↑(Basis.addHaar b) (parallelepiped v) = ENNReal.ofReal |↑(Basis.det b) v|
  have A : parallelepiped v = b.constr ℕ v '' parallelepiped b := by
    rw [image_parallelepiped]
    -- porting note: was `congr 1 with i` but Lean 4 `congr` applies `ext` first
    refine congr_arg _ <| funext fun i ↦ ?_
    exact (b.constr_basis ℕ v i).symm
  rw [A, addHaar_image_linearMap, b.addHaar_self, mul_one, ← LinearMap.det_toMatrix b,
    ← Basis.toMatrix_eq_toMatrix_constr, Basis.det_apply]
#align measure_theory.measure.add_haar_parallelepiped MeasureTheory.Measure.addHaar_parallelepiped

variable [FiniteDimensional ℝ G] {n : ℕ} [_i : Fact (finrank ℝ G = n)]

/-- The Lebesgue measure associated to an alternating map. It gives measure `|ω v|` to the
parallelepiped spanned by the vectors `v₁, ..., vₙ`. Note that it is not always a Haar measure,
as it can be zero, but it is always locally finite and translation invariant. -/
noncomputable irreducible_def _root_.AlternatingMap.measure (ω : AlternatingMap ℝ G ℝ (Fin n)) :
    Measure G :=
  ‖ω (finBasisOfFinrankEq ℝ G _i.out)‖₊ • (finBasisOfFinrankEq ℝ G _i.out).addHaar
#align alternating_map.measure AlternatingMap.measure

theorem _root_.AlternatingMap.measure_parallelepiped (ω : AlternatingMap ℝ G ℝ (Fin n))
    (v : Fin n → G) : ω.measure (parallelepiped v) = ENNReal.ofReal |ω v| := by
  conv_rhs => rw [ω.eq_smul_basis_det (finBasisOfFinrankEq ℝ G _i.out)]
  -- ⊢ ↑↑(AlternatingMap.measure ω) (parallelepiped v) = ENNReal.ofReal |↑(↑ω ↑(fin …
  simp only [addHaar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, Algebra.id.smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    Real.ennnorm_eq_ofReal_abs]
#align alternating_map.measure_parallelepiped AlternatingMap.measure_parallelepiped

instance (ω : AlternatingMap ℝ G ℝ (Fin n)) : IsAddLeftInvariant ω.measure := by
  rw [AlternatingMap.measure]; infer_instance
  -- ⊢ IsAddLeftInvariant (‖↑ω ↑(finBasisOfFinrankEq ℝ G (_ : finrank ℝ G = n))‖₊ • …
                               -- 🎉 no goals

instance (ω : AlternatingMap ℝ G ℝ (Fin n)) : IsLocallyFiniteMeasure ω.measure := by
  rw [AlternatingMap.measure]; infer_instance
  -- ⊢ IsLocallyFiniteMeasure (‖↑ω ↑(finBasisOfFinrankEq ℝ G (_ : finrank ℝ G = n)) …
                               -- 🎉 no goals

end

/-!
### Density points

Besicovitch covering theorem ensures that, for any locally finite measure on a finite-dimensional
real vector space, almost every point of a set `s` is a density point, i.e.,
`μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `1` as `r` tends to `0`
(see `Besicovitch.ae_tendsto_measure_inter_div`).
When `μ` is a Haar measure, one can deduce the same property for any rescaling sequence of sets,
of the form `{x} + r • t` where `t` is a set with positive finite measure, instead of the sequence
of closed balls.

We argue first for the dual property, i.e., if `s` has density `0` at `x`, then
`μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)` tends to `0`. First when `t` is contained in the ball
of radius `1`, in `tendsto_addHaar_inter_smul_zero_of_density_zero_aux1`,
(by arguing by inclusion). Then when `t` is bounded, reducing to the previous one by rescaling, in
`tendsto_addHaar_inter_smul_zero_of_density_zero_aux2`.
Then for a general set `t`, by cutting it into a bounded part and a part with small measure, in
`tendsto_addHaar_inter_smul_zero_of_density_zero`.
Going to the complement, one obtains the desired property at points of density `1`, first when
`s` is measurable in `tendsto_addHaar_inter_smul_one_of_density_one_aux`, and then without this
assumption in `tendsto_addHaar_inter_smul_one_of_density_one` by applying the previous lemma to
the measurable hull `toMeasurable μ s`
-/

theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u ≠ 0) (t_bound : t ⊆ closedBall 0 1) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  have A : Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (eventually_of_forall fun b => zero_le _)
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    apply mul_le_mul_right' (measure_mono (inter_subset_inter_right _ _)) _
    intro y hy
    have : y - x ∈ r • closedBall (0 : E) 1 := by
      apply smul_set_mono t_bound
      simpa [neg_add_eq_sub] using hy
    simpa only [smul_closedBall _ _ zero_le_one, Real.norm_of_nonneg rpos.le,
      mem_closedBall_iff_norm, mul_one, sub_zero, smul_zero]
  have B :
    Tendsto (fun r : ℝ => μ (closedBall x r) / μ ({x} + r • u)) (𝓝[>] 0)
      (𝓝 (μ (closedBall x 1) / μ ({x} + u))) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    have : closedBall x r = {x} + r • closedBall (0 : E) 1 := by
      simp only [_root_.smul_closedBall, Real.norm_of_nonneg rpos.le, zero_le_one, add_zero,
        mul_one, singleton_add_closedBall, smul_zero]
    simp only [this, addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne']
    simp only [addHaar_closedBall_center, image_add_left, measure_preimage_add, singleton_add]
  have C : Tendsto (fun r : ℝ =>
        μ (s ∩ ({x} + r • t)) / μ (closedBall x r) * (μ (closedBall x r) / μ ({x} + r • u)))
      (𝓝[>] 0) (𝓝 (0 * (μ (closedBall x 1) / μ ({x} + u)))) := by
    apply ENNReal.Tendsto.mul A _ B (Or.inr ENNReal.zero_ne_top)
    simp only [ne_eq, not_true, singleton_add, image_add_left, measure_preimage_add, false_or,
      ENNReal.div_eq_top, h'u, false_or_iff, not_and, and_false_iff]
    intro aux
    exact (measure_closedBall_lt_top.ne aux).elim
    -- Porting note: it used to be enough to pass `measure_closedBall_lt_top.ne` to `simp`
    -- and avoid the `intro; exact` dance.
  simp only [zero_mul] at C
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • u)) (𝓝[Ioi 0] 0)  …
  apply C.congr' _
  -- ⊢ (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ (closedBall x r) * (↑↑μ (closedBall  …
  filter_upwards [self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ), a ∈ Ioi 0 → ↑↑μ (s ∩ ({x} + a • t)) / ↑↑μ (closedBall x a) * (↑↑μ …
  rintro r (rpos : 0 < r)
  -- ⊢ ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ (closedBall x r) * (↑↑μ (closedBall x r) / ↑↑μ …
  calc
    μ (s ∩ ({x} + r • t)) / μ (closedBall x r) * (μ (closedBall x r) / μ ({x} + r • u)) =
        μ (closedBall x r) * (μ (closedBall x r))⁻¹ * (μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) :=
      by simp only [div_eq_mul_inv]; ring
    _ = μ (s ∩ ({x} + r • t)) / μ ({x} + r • u) := by
      rw [ENNReal.mul_inv_cancel (measure_closedBall_pos μ x rpos).ne'
          measure_closedBall_lt_top.ne,
        one_mul]
#align measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux1 MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_aux1

theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u ≠ 0) (R : ℝ) (Rpos : 0 < R) (t_bound : t ⊆ closedBall 0 R) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  set t' := R⁻¹ • t with ht'
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • u)) (𝓝[Ioi 0] 0)  …
  set u' := R⁻¹ • u with hu'
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • u)) (𝓝[Ioi 0] 0)  …
  have A : Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    · simp only [h'u, (pow_pos Rpos _).ne', abs_nonpos_iff, addHaar_smul, not_false_iff,
        ENNReal.ofReal_eq_zero, inv_eq_zero, inv_pow, Ne.def, or_self_iff, mul_eq_zero]
    · refine (smul_set_mono t_bound).trans_eq ?_
      rw [smul_closedBall _ _ Rpos.le, smul_zero, Real.norm_of_nonneg (inv_nonneg.2 Rpos.le),
        inv_mul_cancel Rpos.ne']
  have B : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] (R * 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (tendsto_const_nhds.mul tendsto_id).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin]
      intro r rpos
      rw [mul_zero]
      exact mul_pos Rpos rpos
  rw [mul_zero] at B
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • u)) (𝓝[Ioi 0] 0)  …
  apply (A.comp B).congr' _
  -- ⊢ ((fun r => ↑↑μ (s ∩ ({x} + r • t')) / ↑↑μ ({x} + r • u')) ∘ fun r => R * r)  …
  filter_upwards [self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ), a ∈ Ioi 0 → ((fun r => ↑↑μ (s ∩ ({x} + r • R⁻¹ • t)) / ↑↑μ ({x} + …
  rintro r -
  -- ⊢ ((fun r => ↑↑μ (s ∩ ({x} + r • R⁻¹ • t)) / ↑↑μ ({x} + r • R⁻¹ • u)) ∘ fun r  …
  have T : (R * r) • t' = r • t := by
    rw [mul_comm, ht', smul_smul, mul_assoc, mul_inv_cancel Rpos.ne', mul_one]
  have U : (R * r) • u' = r • u := by
    rw [mul_comm, hu', smul_smul, mul_assoc, mul_inv_cancel Rpos.ne', mul_one]
  dsimp
  -- ⊢ ↑↑μ (s ∩ ({x} + (R * r) • R⁻¹ • t)) / ↑↑μ ({x} + (R * r) • R⁻¹ • u) = ↑↑μ (s …
  rw [T, U]
  -- 🎉 no goals
#align measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux2 MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_aux2

/-- Consider a point `x` at which a set `s` has density zero, with respect to closed balls. Then it
also has density zero with respect to any measurable set `t`: the proportion of points in `s`
belonging to a rescaled copy `{x} + r • t` of `t` tends to zero as `r` tends to zero. -/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (ht : MeasurableSet t) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) := by
  refine' tendsto_order.2 ⟨fun a' ha' => (ENNReal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => _⟩
  -- ⊢ ∀ᶠ (b : ℝ) in 𝓝[Ioi 0] 0, ↑↑μ (s ∩ ({x} + b • t)) / ↑↑μ ({x} + b • t) < ε
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  -- ⊢ ∀ᶠ (b : ℝ) in 𝓝[Ioi 0] 0, ↑↑μ (s ∩ ({x} + b • t)) / ↑↑μ ({x} + b • t) < ε
  · apply eventually_of_forall fun r => ?_
    -- ⊢ ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • t) < ε
    suffices H : μ (s ∩ ({x} + r • t)) = 0
    -- ⊢ ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • t) < ε
    · rw [H]; simpa only [ENNReal.zero_div] using εpos
      -- ⊢ 0 / ↑↑μ ({x} + r • t) < ε
              -- 🎉 no goals
    apply le_antisymm _ (zero_le _)
    -- ⊢ ↑↑μ (s ∩ ({x} + r • t)) ≤ 0
    calc
      μ (s ∩ ({x} + r • t)) ≤ μ ({x} + r • t) := measure_mono (inter_subset_right _ _)
      _ = 0 := by
        simp only [h't, addHaar_smul, image_add_left, measure_preimage_add, singleton_add,
          mul_zero]
  obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ μ (t \ closedBall 0 n) < ε / 2 * μ t := by
    have A :
      Tendsto (fun n : ℕ => μ (t \ closedBall 0 n)) atTop
        (𝓝 (μ (⋂ n : ℕ, t \ closedBall 0 n))) := by
      have N : ∃ n : ℕ, μ (t \ closedBall 0 n) ≠ ∞ :=
        ⟨0, ((measure_mono (diff_subset t _)).trans_lt h''t.lt_top).ne⟩
      refine' tendsto_measure_iInter (fun n ↦ ht.diff measurableSet_closedBall) (fun m n hmn ↦ _) N
      exact diff_subset_diff Subset.rfl (closedBall_subset_closedBall (Nat.cast_le.2 hmn))
    have : ⋂ n : ℕ, t \ closedBall 0 n = ∅ := by
      simp_rw [diff_eq, ← inter_iInter, iInter_eq_compl_iUnion_compl, compl_compl,
        iUnion_closedBall_nat, compl_univ, inter_empty]
    simp only [this, measure_empty] at A
    have I : 0 < ε / 2 * μ t := ENNReal.mul_pos (ENNReal.half_pos εpos.ne').ne' h't
    exact (Eventually.and (Ioi_mem_atTop 0) ((tendsto_order.1 A).2 _ I)).exists
  have L :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) / μ ({x} + r • t)) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 μ s x h _ t h't n (Nat.cast_pos.2 npos)
      (inter_subset_right _ _)
  filter_upwards [(tendsto_order.1 L).2 _ (ENNReal.half_pos εpos.ne'), self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ), ↑↑μ (s ∩ ({x} + a • (t ∩ closedBall 0 ↑n))) / ↑↑μ ({x} + a • t) < …
  rintro r hr (rpos : 0 < r)
  -- ⊢ ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • t) < ε
  have I :
    μ (s ∩ ({x} + r • t)) ≤
      μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n)) :=
    calc
      μ (s ∩ ({x} + r • t)) =
          μ (s ∩ ({x} + r • (t ∩ closedBall 0 n)) ∪ s ∩ ({x} + r • (t \ closedBall 0 n))) :=
        by rw [← inter_union_distrib_left, ← add_union, ← smul_set_union, inter_union_diff]
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ (s ∩ ({x} + r • (t \ closedBall 0 n))) :=
        (measure_union_le _ _)
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n)) :=
        add_le_add le_rfl (measure_mono (inter_subset_right _ _))
  calc
    μ (s ∩ ({x} + r • t)) / μ ({x} + r • t) ≤
        (μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n))) /
          μ ({x} + r • t) :=
      mul_le_mul_right' I _
    _ < ε / 2 + ε / 2 := by
      rw [ENNReal.add_div]
      apply ENNReal.add_lt_add hr _
      rwa [addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne',
        ENNReal.div_lt_iff (Or.inl h't) (Or.inl h''t)]
    _ = ε := ENNReal.add_halves _
#align measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero

theorem tendsto_addHaar_inter_smul_one_of_density_one_aux (s : Set E) (hs : MeasurableSet s)
    (x : E) (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1))
    (t : Set E) (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have I : ∀ u v, μ u ≠ 0 → μ u ≠ ∞ → MeasurableSet v →
    μ u / μ u - μ (vᶜ ∩ u) / μ u = μ (v ∩ u) / μ u := by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.sub_mul]; swap
    · simp only [uzero, ENNReal.inv_eq_top, imp_true_iff, Ne.def, not_false_iff]
    congr 1
    apply
      ENNReal.sub_eq_of_add_eq (ne_top_of_le_ne_top utop (measure_mono (inter_subset_right _ _)))
    rw [inter_comm _ u, inter_comm _ u]
    exact measure_inter_add_diff u vmeas
  have L : Tendsto (fun r => μ (sᶜ ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    have A : Tendsto (fun r => μ (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr' _
      filter_upwards [self_mem_nhdsWithin]
      intro r hr
      rw [div_eq_mul_inv, ENNReal.mul_inv_cancel]
      · exact (measure_closedBall_pos μ _ hr).ne'
      · exact measure_closedBall_lt_top.ne
    have B := ENNReal.Tendsto.sub A h (Or.inl ENNReal.one_ne_top)
    simp only [tsub_self] at B
    apply B.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    convert I (closedBall x r) sᶜ (measure_closedBall_pos μ _ rpos).ne'
      measure_closedBall_lt_top.ne hs.compl
    rw [compl_compl]
  have L' : Tendsto (fun r : ℝ => μ (sᶜ ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_addHaar_inter_smul_zero_of_density_zero μ sᶜ x L t ht h''t
  have L'' : Tendsto (fun r : ℝ => μ ({x} + r • t) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    rw [addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne', ENNReal.div_self h't h''t]
  have := ENNReal.Tendsto.sub L'' L' (Or.inl ENNReal.one_ne_top)
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • t)) (𝓝[Ioi 0] 0)  …
  simp only [tsub_zero] at this
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • t)) (𝓝[Ioi 0] 0)  …
  apply this.congr' _
  -- ⊢ (fun a => ↑↑μ ({x} + a • t) / ↑↑μ ({x} + a • t) - ↑↑μ (sᶜ ∩ ({x} + a • t)) / …
  filter_upwards [self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ), a ∈ Ioi 0 → ↑↑μ ({x} + a • t) / ↑↑μ ({x} + a • t) - ↑↑μ (sᶜ ∩ ({x …
  rintro r (rpos : 0 < r)
  -- ⊢ ↑↑μ ({x} + r • t) / ↑↑μ ({x} + r • t) - ↑↑μ (sᶜ ∩ ({x} + r • t)) / ↑↑μ ({x}  …
  refine' I ({x} + r • t) s _ _ hs
  -- ⊢ ↑↑μ ({x} + r • t) ≠ 0
  · simp only [h't, abs_of_nonneg rpos.le, pow_pos rpos, addHaar_smul, image_add_left,
      ENNReal.ofReal_eq_zero, not_le, or_false_iff, Ne.def, measure_preimage_add, abs_pow,
      singleton_add, mul_eq_zero]
  · simp [h''t, ENNReal.ofReal_ne_top, addHaar_smul, image_add_left, ENNReal.mul_eq_top,
      Ne.def, not_false_iff, measure_preimage_add, singleton_add, and_false_iff, false_and_iff,
      or_self_iff]
#align measure_theory.measure.tendsto_add_haar_inter_smul_one_of_density_one_aux MeasureTheory.Measure.tendsto_addHaar_inter_smul_one_of_density_one_aux

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any
measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t`
of `t` tends to one as `r` tends to zero. -/
theorem tendsto_addHaar_inter_smul_one_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have : Tendsto (fun r : ℝ => μ (toMeasurable μ s ∩ ({x} + r • t)) / μ ({x} + r • t))
    (𝓝[>] 0) (𝓝 1) := by
    apply
      tendsto_addHaar_inter_smul_one_of_density_one_aux μ _ (measurableSet_toMeasurable _ _) _ _
        t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
    · refine' eventually_of_forall fun r => mul_le_mul_right' _ _
      exact measure_mono (inter_subset_inter_left _ (subset_toMeasurable _ _))
    · filter_upwards [self_mem_nhdsWithin]
      rintro r -
      apply ENNReal.div_le_of_le_mul
      rw [one_mul]
      exact measure_mono (inter_subset_right _ _)
  refine this.congr fun r => ?_
  -- ⊢ ↑↑μ (toMeasurable μ s ∩ ({x} + r • t)) / ↑↑μ ({x} + r • t) = ↑↑μ (s ∩ ({x} + …
  congr 1
  -- ⊢ ↑↑μ (toMeasurable μ s ∩ ({x} + r • t)) = ↑↑μ (s ∩ ({x} + r • t))
  apply measure_toMeasurable_inter_of_sigmaFinite
  -- ⊢ MeasurableSet ({x} + r • t)
  simp only [image_add_left, singleton_add]
  -- ⊢ MeasurableSet ((fun x_1 => -x + x_1) ⁻¹' (r • t))
  apply (continuous_add_left (-x)).measurable (ht.const_smul₀ r)
  -- 🎉 no goals
#align measure_theory.measure.tendsto_add_haar_inter_smul_one_of_density_one MeasureTheory.Measure.tendsto_addHaar_inter_smul_one_of_density_one

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` intersects the rescaled copies `{x} + r • t` of a given
set `t` with positive measure, for any small enough `r`. -/
theorem eventually_nonempty_inter_smul_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • t)).Nonempty := by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : ∃ t', MeasurableSet t' ∧ t' ⊆ t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_addHaar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
      0 zero_lt_one]
  intro r hr
  -- ⊢ Set.Nonempty (s ∩ ({x} + r • t))
  have : μ (s ∩ ({x} + r • t')) ≠ 0 := fun h' => by
    simp only [ENNReal.not_lt_zero, ENNReal.zero_div, h'] at hr
  have : (s ∩ ({x} + r • t')).Nonempty := nonempty_of_measure_ne_zero this
  -- ⊢ Set.Nonempty (s ∩ ({x} + r • t))
  apply this.mono (inter_subset_inter Subset.rfl _)
  -- ⊢ {x} + r • t' ⊆ {x} + r • t
  exact add_subset_add Subset.rfl (smul_set_mono t't)
  -- 🎉 no goals
#align measure_theory.measure.eventually_nonempty_inter_smul_of_density_one MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one

end Measure

end MeasureTheory
