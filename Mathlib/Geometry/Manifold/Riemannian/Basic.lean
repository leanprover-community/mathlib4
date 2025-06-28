/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with an
inner product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths. -/

open Bundle Bornology Set MeasureTheory Manifold Filter
open scoped ENNReal ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section

variable [EMetricSpace M] [ChartedSpace H M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I M) in
/-- Consider a manifold in which the tangent spaces are already endowed with an inner product, and
the space is already endowed with an extended distance. We say that this is a Riemannian manifold
if the distance is given by the infimum of the lengths of `C^1` paths, measured using the norm in
the tangent spaces.

This is a `Prop` valued typeclass, on top of existing data. -/
class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

end

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (F) in
/-- The standard riemannian metric on a vector space with an inner product, given by this inner
product on each tangent space. -/
noncomputable def riemannianMetricVectorSpace :
    ContMDiffRiemannianMetric 𝓘(ℝ, F) ω F (fun (x : F) ↦ TangentSpace 𝓘(ℝ, F) x) where
  inner x := (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)
  symm x v w := real_inner_comm  _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √ 1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← this]
    exact NormedSpace.isVonNBounded_ball ℝ F 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := innerSL ℝ)
    ext v w
    simp? [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        Trivialization.linearMapAt_apply] says
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        TangentBundle.symmL_model_space, ContinuousLinearMap.coe_comp',
        Trivialization.continuousLinearMapAt_apply, Function.comp_apply,
        Trivialization.linearMapAt_apply, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet, PartialHomeomorph.refl_partialEquiv,
        PartialEquiv.refl_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
        Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, inter_self, mem_univ,
        ↓reduceIte, Trivial.trivialization_apply]
    rfl

noncomputable instance : RiemannianBundle (fun (x : F) ↦ TangentSpace 𝓘(ℝ, F) x) :=
  ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

lemma norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ = ‖show F from v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]

lemma nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖₊ = ‖show F from v‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

lemma enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ₑ = ‖show F from v‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

open MeasureTheory Measure

lemma lintegral_fderiv_lineMap_eq_edist {x y : E} :
    ∫⁻ t in Icc 0 1, ‖fderivWithin ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) (Icc 0 1) t 1‖ₑ
      = edist x y := by
  have : edist x y = ∫⁻ t in Icc (0 : ℝ) 1, ‖y - x‖ₑ := by
    simp [edist_comm x y, edist_eq_enorm_sub]
  rw [this]
  apply setLIntegral_congr_fun measurableSet_Icc (fun z hz ↦ ?_)
  rw [show y - x = fderiv ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) z 1 by simp]
  congr
  exact fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one _ hz)
    (ContinuousAffineMap.differentiableAt _)

/-- An inner product vector space is a Riemannian manifold, i.e., the distance between two points
is the infimum of the lengths of paths between these points. -/
instance : IsRiemannianManifold 𝓘(ℝ, F) F := by
  refine ⟨fun x y ↦ le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : ℝ → F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContDiffOn ℝ 1 e (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp (hγ.comp_contMDiffOn contMDiffOn_projIcc)
    rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc,
      pathELength_eq_lintegral_mfderivWithin_Icc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    conv_lhs =>
      rw [edist_comm, edist_eq_enorm_sub, show x = e 0 by simp [e], show y = e 1 by simp [e]]
    exact (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc D zero_le_one).trans_eq rfl
  · let γ := ContinuousAffineMap.lineMap (R := ℝ) x y
    have : riemannianEDist 𝓘(ℝ, F) x y ≤ pathELength 𝓘(ℝ, F) γ 0 1 := by
      apply riemannianEDist_le_pathELength ?_ (by simp [γ, ContinuousAffineMap.coe_lineMap_eq])
        (by simp [γ, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
      rw [contMDiffOn_iff_contDiffOn]
      exact γ.contDiff.contDiffOn
    apply this.trans_eq
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    exact lintegral_fderiv_lineMap_eq_edist

end

open Manifold Metric
open scoped NNReal

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
[IsManifold I 1 M]
[IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

section

/-- Register on the tangent space to a normed vector space the same `NormedAddCommGroup` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the Riemannian
structure for inner product spaces, but can be activated locally. -/
def normedAddCommGroupTangentSpaceVectorSpace (x : E) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- Register on the tangent space to a normed vector space the same `NormedSpace` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the Riemannian
structure for inner product spaces, but can be activated locally. -/
def normedSpaceTangentSpaceVectorSpace (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

attribute [local instance] normedSpaceTangentSpaceVectorSpace

variable (I)

lemma eventually_norm_mfderiv_extChartAt_lt (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x) y‖ < C := by
  rcases eventually_norm_trivializationAt_lt E (fun (x : M) ↦ TangentSpace I x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source ∈ 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rwa [← TangentBundle.continuousLinearMapAt_trivializationAt h'y]

lemma eventually_enorm_mfderiv_extChartAt_lt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝 x,
    ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x) y‖ₑ < C := by
  rcases eventually_norm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to ℝ≥0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

lemma eventually_norm_mfderivWithin_symm_extChartAt_comp_lt (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x,
    ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (extChartAt I x y)‖ < C := by
  rcases eventually_norm_symmL_trivializationAt_lt E (fun (x : M) ↦ TangentSpace I x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source ∈ 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rw [TangentBundle.symmL_trivializationAt h'y] at hy
  have A : (extChartAt I x).symm (extChartAt I x y) = y :=
    (extChartAt I x).left_inv (by simpa using h'y)
  convert hy using 3 <;> congr

lemma eventually_norm_mfderivWithin_symm_extChartAt_lt (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝[range I] (extChartAt I x x),
    ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ < C := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by simp
  rw [this] at hC
  have : ContinuousAt (extChartAt I x).symm (extChartAt I x x) := continuousAt_extChartAt_symm _
  filter_upwards [nhdsWithin_le_nhds (this.preimage_mem_nhds hC),
    extChartAt_target_mem_nhdsWithin x] with y hy h'y
  have : y = (extChartAt I x) ((extChartAt I x).symm y) := by simp [-extChartAt, h'y]
  simp [-extChartAt] at hy
  convert hy

lemma eventually_enorm_mfderivWithin_symm_extChartAt_lt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝[range I] (extChartAt I x x),
    ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ₑ < C := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to ℝ≥0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

/-- Around any point `x`, the Riemannian distance between two points is controlled by the distance
in the extended chart. In other words, the extended chart is locally Lipschitz. -/
lemma eventually_riemannianEDist_le_edist_extChartAt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝 x,
    riemannianEDist I x y ≤ C * edist (extChartAt I x x) (extChartAt I x y) := by
  /- To construct a path with controlled distance from `x` to `y`, we consider the segment from
  `extChartAt x x` to `extChartAt x y` in the chart, and we push it by `(extChartAt x).symm`. As
  the derivative of the latter is locally bounded, this only multiplies the length by a bounded
  amount. -/
  -- first start from a bound on the derivative
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  -- consider a small convex set around `extChartAt x x` where everything is controlled.
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ₑ < C} :=
    mem_nhdsWithin_iff.1 (Filter.inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  -- pull this set inside `M`: this is the set where we will get the estimate.
  have A : (extChartAt I x) ⁻¹' (ball (extChartAt I x x) r ∩ range I) ∈ 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ r_pos)
  -- consider `y` in this good set. Let `η` be the segment in the extended chart, and
  -- `γ` its composition with `(extChartAt x).symm`.
  filter_upwards [A, chart_source_mem_nhds H x] with y hy h'y
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt I x x) (extChartAt I x y)
  set γ := (extChartAt I x).symm ∘ η
  -- by convexity, the whole segment between `extChartAt x x` and `extChartAt x y` is in the
  -- controlled set.
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
        {y | ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ₑ < C}) := by
    simp only [← preimage_inter, ← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter I.convex_range).segment_subset (by simp [r_pos]) hy
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  -- we can bound the Riemannian distance using the specific path `γ`.
  have : riemannianEDist I x y ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, h'y]
  apply this.trans
  -- Finally, we control the length of `γ` thanks to the boundedness of the derivative of
  -- `(extChartAt x).symm` on the whole controlled set.
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have : mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (η t)) ∘L
      (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc 0 1) t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn le_rfl t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have : mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t 1 =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (η t))
      (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc 0 1) t 1) := by
    rw [this]
    rfl
  rw [this]
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

/-- If points are close for the topology, then their Riemannian distance is small. -/
lemma eventually_riemmanianEDist_lt (x : M) {c : ℝ≥0∞} (hc : 0 < c) :
    ∀ᶠ y in 𝓝 x, riemannianEDist I x y < c := by
  rcases eventually_riemannianEDist_le_edist_extChartAt I x with ⟨C, C_pos, hC⟩
  have : (extChartAt I x) ⁻¹' (EMetric.ball (extChartAt I x x) (c / C)) ∈ 𝓝 x := by
    apply (continuousAt_extChartAt x).preimage_mem_nhds
    exact EMetric.ball_mem_nhds _ (ENNReal.div_pos hc.ne' (by simp))
  filter_upwards [this, hC] with y hy h'y
  apply h'y.trans_lt
  have : edist (extChartAt I x x) (extChartAt I x y) < c / C := by
    simpa only [mem_preimage, EMetric.mem_ball'] using hy
  rwa [ENNReal.lt_div_iff_mul_lt, mul_comm] at this
  · exact Or.inl (mod_cast C_pos.ne')
  · simp

/-- Any neighborhood of `x` contains all the points which are close enough to `x` for the
Riemannian distance. -/
lemma setOf_riemmanianEDist_lt_subset_nhds [RegularSpace M] {x : M} {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ c > (0 : ℝ≥0), {y | riemannianEDist I x y < c} ⊆ s := by
  rcases eventually_enorm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  obtain ⟨u, u_mem, u_closed, us, hu, uc⟩ : ∃ u ∈ 𝓝 x, IsClosed u ∧ u ⊆ s
      ∧ u ⊆ {y | ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x) y‖ₑ < C} ∧ u ⊆ (extChartAt I x).source := by
    have W := Filter.inter_mem (Filter.inter_mem hs hC) (extChartAt_source_mem_nhds (I := I) x)
    rcases exists_mem_nhds_isClosed_subset W with ⟨u, u_mem, u_closed, hu⟩
    simp only [subset_inter_iff] at hu
    exact ⟨u, u_mem, u_closed, hu.1.1, hu.1.2, hu.2⟩
  have uc' : u ⊆ (chartAt H x).source := by simpa [extChartAt_source I x] using uc
  obtain ⟨v, v_mem, v_open, hv⟩ : ∃ v ∈ 𝓝 x, IsOpen v ∧ v ⊆ u := by
    rcases _root_.mem_nhds_iff.1 u_mem with ⟨v, vu, v_open, xv⟩
    refine ⟨v, v_open.mem_nhds xv, v_open, vu⟩
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0, ball (extChartAt I x x) r ⊆ (extChartAt I x).symm ⁻¹' v :=
    Metric.mem_nhds_iff.1 (extChartAt_preimage_mem_nhds v_mem)
  lift r to ℝ≥0 using r_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at r_pos
  refine ⟨r / C, by positivity, ?_⟩
  intro y hy
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
    with ⟨γ, hγx, hγy, γ_smooth, hγ, -⟩
  let a := {t ∈ Icc 0 1 | ∀ t' ∈ Icc 0 t, γ t' ∈ u}
  have zero_mem : 0 ∈ a := by simpa only [mem_setOf_eq, Icc_self, mem_singleton_iff, forall_eq, a,
    hγx, left_mem_Icc, zero_le_one, true_and] using mem_of_mem_nhds u_mem
  have bdd_a : BddAbove a := ⟨1, fun t ht ↦ ht.1.2⟩
  have sup_mem : sSup a ∈ a := by
    rcases exists_seq_tendsto_sSup (S := a) ⟨0, zero_mem⟩ bdd_a with ⟨z, z_mono, z_lim, hz⟩
    refine ⟨?_, fun t ht ↦ ?_⟩
    · apply IsClosed.mem_of_tendsto isClosed_Icc z_lim (Eventually.of_forall (fun n ↦ (hz n).1))
    rcases ht.2.eq_or_lt with rfl | h
    · have : Tendsto (fun n ↦ γ (z n)) atTop (𝓝 (γ (sSup a))) :=
        (γ_smooth.continuous.tendsto (sSup a)).comp z_lim
      apply u_closed.mem_of_tendsto this (Eventually.of_forall (fun n ↦ ?_))
      exact (hz n).2 _ ⟨(hz n).1.1, le_rfl⟩
    · obtain ⟨n, hn⟩ : ∃ n, t < z n := ((tendsto_order.1 z_lim).1 _ h).exists
      exact (hz n).2 t ⟨ht.1, hn.le⟩
  have B (t) (ht : t ∈ a) : γ t ∈ v := by
    let γ' := (extChartAt I x) ∘ γ
    have hC : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ' (Icc 0 t) :=
      ContMDiffOn.comp (I' := I) (t := (chartAt H x).source) contMDiffOn_extChartAt
        γ_smooth.contMDiffOn (fun t' ht' ↦ uc' (ht.2 t' ht'))
    have : ‖γ' t - γ' 0‖ₑ < r := calc
        ‖γ' t - γ' 0‖ₑ
      _ ≤ ∫⁻ t' in Icc 0 t, ‖derivWithin γ' (Icc 0 t) t'‖ₑ := by
        apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ ht.1.1
        rwa [← contMDiffOn_iff_contDiffOn]
      _ = ∫⁻ t' in Icc 0 t, ‖mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ' (Icc 0 t) t' 1‖ₑ := by
        simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        rfl
      _ ≤ ∫⁻ t' in Icc 0 t, C * ‖mfderivWithin 𝓘(ℝ) I γ (Icc 0 t) t' 1‖ₑ := by
        rcases ht.1.1.eq_or_lt with rfl | h't
        · simp
        apply setLIntegral_mono' measurableSet_Icc (fun t' ht' ↦ ?_)
        have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ' (Icc 0 t) t' =
            (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (γ t')) ∘L
            (mfderivWithin 𝓘(ℝ) I γ (Icc 0 t) t') := by
          apply mfderiv_comp_mfderivWithin
          · exact mdifferentiableAt_extChartAt (uc' (ht.2 t' ht'))
          · exact (γ_smooth.mdifferentiable le_rfl).mdifferentiableOn _ ht'
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc h't _ ht'
        have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ' (Icc 0 t) t' 1 =
            (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (γ t'))
            (mfderivWithin 𝓘(ℝ) I γ (Icc 0 t) t' 1) := by rw [this]; rfl
        rw [this]
        apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
        gcongr





      _ = C * pathELength I γ 0 t := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, pathELength_eq_lintegral_mfderivWithin_Icc]
      _ ≤ C * pathELength I γ 0 1 := by
        gcongr
        exact pathELength_mono le_rfl ht.1.2
      _ < C * (r / C) := by
        gcongr
        · exact ENNReal.coe_ne_top
        · exact hγ.trans_eq (ENNReal.coe_div C_pos.ne')
      _ = r := (ENNReal.eq_div_iff (by simpa using C_pos.ne') ENNReal.coe_ne_top).mp rfl
    sorry
  sorry

#exit















#exit

exact (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc D zero_le_one).trans_eq rfl














end
