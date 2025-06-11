/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with a
scalar product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths. -/

open Bundle Bornology Set
open scoped Manifold ENNReal ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance (x : ℝ) : One (TangentSpace 𝓘(ℝ) x) where
  one := (1 : ℝ)

/-- Unit vector in the tangent space to a segment, as the image of the unit vector in the real line
under the canonical projection. It is also mapped to the unit vector in the real line through
the canonical injection, see `mfderiv_subtypeVal_Icc_one`.

Note that one can not abuse defeqs for this definition: this is *not* the same as the vector
`fun _ ↦ 1` in `EuclideanSpace ℝ (Fin 1)` through defeqs, as one of the charts of `Icc x y` is
orientation-reversing. -/
irreducible_def one_tangentSpace_Icc {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    TangentSpace (𝓡∂ 1) z :=
  mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (Set.projIcc x y h.out.le) (Icc x y) z 1

instance {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) : One (TangentSpace (𝓡∂ 1) z) where
  one := one_tangentSpace_Icc z

section ToMove

/-- The inclusion map from of a closed segment to `ℝ` is smooth in the manifold sense. -/
lemma contMDiff_subtypeVal_Icc {x y : ℝ} [h : Fact (x < y)] {n : WithTop ℕ∞} :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨by fun_prop, ?_⟩
  simp? says
    simp only [extChartAt, PartialHomeomorph.extend, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.refl_coe,
      Icc_chartedSpaceChartAt, unitInterval.coe_lt_one, PartialEquiv.coe_trans_symm,
      PartialHomeomorph.coe_coe_symm, ModelWithCorners.toPartialEquiv_coe_symm, CompTriple.comp_eq,
      PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
      Function.comp_apply]
  split_ifs with hz
  · simp? [IccLeftChart, Function.comp_def, modelWithCornersEuclideanHalfSpace] says
      simp only [IccLeftChart, Fin.isValue, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk,
      modelWithCornersEuclideanHalfSpace, ModelWithCorners.mk_symm, Function.comp_def,
      Function.update_self, ModelWithCorners.mk_coe, PartialHomeomorph.mk_coe]
    rw [Subtype.range_val_subtype]
    have : ContDiff ℝ n (fun (z : EuclideanSpace ℝ (Fin 1)) ↦ z 0 + x) := by fun_prop
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem; swap
    · simpa using z.2.1
    have : {w : EuclideanSpace ℝ (Fin 1) | w 0 < y - x} ∈ 𝓝 (fun i ↦ z - x) := by
      apply (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds
      simpa using hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with w hw h'w
    rw [max_eq_left hw, min_eq_left]
    linarith
  · simp only [not_lt] at hz
    simp? [IccRightChart, Function.comp_def, modelWithCornersEuclideanHalfSpace] says
      simp only [IccRightChart, Fin.isValue, PartialHomeomorph.mk_coe_symm,
        PartialEquiv.coe_symm_mk, modelWithCornersEuclideanHalfSpace, ModelWithCorners.mk_symm,
        Function.comp_def, Function.update_self, ModelWithCorners.mk_coe, PartialHomeomorph.mk_coe]
    rw [Subtype.range_val_subtype]
    have : ContDiff ℝ n (fun (z : EuclideanSpace ℝ (Fin 1)) ↦ y - z 0) := by fun_prop
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem; swap
    · simpa using z.2.2
    have : {w : EuclideanSpace ℝ (Fin 1) | w 0 < y - x} ∈ 𝓝 (fun i ↦ y - z) := by
      apply (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds
      simpa using h.out.trans_le hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with w hw h'w
    rw [max_eq_left hw, max_eq_left]
    linarith

/-- The projection from `ℝ` to a closed segment is smooth on the segment, in the manifold sense. -/
lemma contMDiffOn_projIcc {x y : ℝ} [h : Fact (x < y)] {n : WithTop ℕ∞} :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) n (Set.projIcc x y h.out.le) (Icc x y) := by
  intro z hz
  rw [contMDiffWithinAt_iff]
  refine ⟨by apply ContinuousAt.continuousWithinAt; fun_prop, ?_⟩
  simp? says
    simp only [extChartAt, PartialHomeomorph.extend, Icc_chartedSpaceChartAt,
      PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq,
      preimage_id_eq, id_eq, modelWithCornersSelf_coe, range_id, inter_univ]
  split_ifs with h'z
  · simp? [IccLeftChart, Function.comp_def, modelWithCornersEuclideanHalfSpace, projIcc] says
      simp only [modelWithCornersEuclideanHalfSpace, Fin.isValue, ModelWithCorners.mk_coe,
        IccLeftChart, PartialHomeomorph.mk_coe, Function.comp_def, projIcc]
    have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from fun (_ : Fin 1) ↦ w - x)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    simp only [sub_left_inj]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]
  · simp? [IccRightChart, Function.comp_def, modelWithCornersEuclideanHalfSpace, projIcc] says
      simp only [modelWithCornersEuclideanHalfSpace, Fin.isValue, ModelWithCorners.mk_coe,
        IccRightChart, PartialHomeomorph.mk_coe, Function.comp_def, projIcc]
    have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from fun (_ : Fin 1) ↦ y - w)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    simp only [sub_left_inj]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]

lemma contMDiffOn_comp_projIcc_iff {x y : ℝ} [h : Fact (x < y)] {n : WithTop ℕ∞} (f : Icc x y → M) :
    ContMDiffOn 𝓘(ℝ) I n (f ∘ (Set.projIcc x y h.out.le)) (Icc x y) ↔ ContMDiff (𝓡∂ 1) I n f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp_contMDiffOn contMDiffOn_projIcc⟩
  convert hf.comp_contMDiff (contMDiff_subtypeVal_Icc (x := x) (y := y)) (fun z ↦ z.2)
  ext z
  simp

lemma mfderivWithin_projIcc_one {x y : ℝ} [h : Fact (x < y)] (z : ℝ) (hz : z ∈ Icc x y) :
    mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (Set.projIcc x y h.out.le) (Icc x y) z 1 = 1 := by
  change _ = one_tangentSpace_Icc (Set.projIcc x y h.out.le z)
  simp [one_tangentSpace_Icc]
  congr
  simp only [projIcc_of_mem h.out.le hz]

lemma mfderiv_subtypeVal_Icc_one {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z 1 = 1 := by
  have A : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (Subtype.val ∘ (projIcc x y h.out.le)) (Icc x y) z 1
      = mfderivWithin 𝓘(ℝ) 𝓘(ℝ) id (Icc x y) z 1 := by
    congr 1
    apply mfderivWithin_congr_of_mem _ z.2
    intro z hz
    simp [projIcc_of_mem h.out.le hz]
  rw [mfderiv_comp_mfderivWithin (I' := 𝓡∂ 1)] at A; rotate_left
  · apply contMDiff_subtypeVal_Icc.mdifferentiableAt le_rfl
  · apply (contMDiffOn_projIcc _ z.2).mdifferentiableWithinAt le_rfl
  · apply (uniqueDiffOn_Icc h.out _ z.2).uniqueMDiffWithinAt
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp', id_eq,
    mfderivWithin_eq_fderivWithin, mfderivWithin_projIcc_one z z.2] at A
  have : projIcc x y h.out.le z = z := by simp only [projIcc_of_mem h.out.le z.2]
  rw [this] at A
  convert A
  rw [fderivWithin_id (uniqueDiffOn_Icc h.out _ z.2)]
  rfl

end ToMove


section

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an inner product, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I 1 γ), ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ

/- TODO: show that this is a distance (symmetry, triange inequality, nondegeneracy) -/

end

section

variable [EMetricSpace M] [ChartedSpace H M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I M) in
/-- Consider a manifold in which the tangent spaces are already endowed with a scalar product, and
already endowed with an extended distance. We say that this is a Riemannian manifold if the distance
is given by the infimum of the lengths of `C^1` paths, measured using the norm in the tangent
spaces.

This is a `Prop` valued typeclass, on top of existing data. -/
class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

/- TODO: show that a vector space with an inner product is a Riemannian manifold. -/

end

section

open Bundle

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
        Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_self,
        Set.mem_univ, ↓reduceIte, Trivial.trivialization_apply]
    rfl

noncomputable instance : RiemannianBundle (fun (x : F) ↦ TangentSpace 𝓘(ℝ, F) x) :=
  ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

set_option synthInstance.maxHeartbeats 30000 in
-- otherwise, the instance is not found!
lemma norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ = ‖show F from v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]

set_option synthInstance.maxHeartbeats 30000 in
-- otherwise, the instance is not found!
lemma nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖₊ = ‖show F from v‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

lemma enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ₑ = ‖show F from v‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

open MeasureTheory Measure

instance : IsRiemannianManifold 𝓘(ℝ, F) F := by
  refine ⟨fun x y ↦ le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : ℝ → F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, F) 1 e (Icc 0 1) :=
      hγ.comp_contMDiffOn contMDiffOn_projIcc
    have A (x : Icc 0 1) : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, F) e (Icc 0 1) x 1
        = mfderiv (𝓡∂ 1) 𝓘(ℝ, F) γ x 1 := by
      simp only [e]
      rw [mfderiv_comp_mfderivWithin (I' := 𝓡∂ 1)]; rotate_left
      · apply hγ.mdifferentiableAt le_rfl
      · apply (contMDiffOn_projIcc _ x.2).mdifferentiableWithinAt le_rfl
      · apply (uniqueDiffOn_Icc zero_lt_one _ x.2).uniqueMDiffWithinAt
      simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
      have I : projIcc 0 1 zero_le_one (x : ℝ) = x := by rw [projIcc_of_mem]
      have J : x = projIcc 0 1 zero_le_one (x : ℝ) := by rw [I]
      rw [I]
      congr 1
      convert mfderivWithin_projIcc_one x x.2
    have : ∫⁻ x, ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, F) γ x 1‖ₑ
        = ∫⁻ x in Icc 0 1, ‖mfderivWithin 𝓘(ℝ) 𝓘(ℝ, F) e (Icc 0 1) x 1‖ₑ := by
      simp_rw [← A]
      have : MeasurePreserving (Subtype.val : unitInterval → ℝ) volume
        (volume.restrict (Icc 0 1)) := measurePreserving_subtype_coe measurableSet_Icc
      rw [← MeasureTheory.MeasurePreserving.lintegral_comp_emb this]
      apply MeasurableEmbedding.subtype_coe measurableSet_Icc
    rw [this]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    rw [edist_comm, edist_eq_enorm_sub, show x = e 0 by simp [e], show y = e 1 by simp [e]]
    have D' : ContDiffOn ℝ 1 e (Icc 0 1) := contMDiffOn_iff_contDiffOn.mp D
    exact (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc D' zero_le_one).trans_eq rfl
  · let γ := Path.segment x y
    have : ContMDiff (𝓡∂ 1) 𝓘(ℝ, F) 1 γ := by
      rw [← contMDiffOn_comp_projIcc_iff]
      simp only [Path.segment, Path.coe_mk', ContinuousMap.coe_mk, contMDiffOn_iff_contDiffOn, γ]
      have : ContDiff ℝ 1 (AffineMap.lineMap (k := ℝ) x y) := by
        change ContDiff ℝ 1 (ContinuousAffineMap.lineMap (k := ℝ) x y)









end
