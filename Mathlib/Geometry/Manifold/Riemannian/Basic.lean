/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Constructions.UnitInterval

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
  {M : Type*}

instance (x : ℝ) : One (TangentSpace 𝓘(ℝ) x) where
  one := (1 : ℝ)

irreducible_def one_tangentSpace_Icc {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    TangentSpace (𝓡∂ 1) z :=
  mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (Set.projIcc x y h.out.le) (Icc x y) z 1

instance {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) : One (TangentSpace (𝓡∂ 1) z) where
  one := one_tangentSpace_Icc z

section

variable [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an inner product, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I 1 γ), ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ

/- TODO: show that this is a distance (symmetry, triange inequality, nondegeneracy) -/

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

lemma mfderivWithin_projIcc_one {x y : ℝ} [h : Fact (x < y)] (z : ℝ) (hz : z ∈ Icc x y) :
    mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (Set.projIcc x y h.out.le) (Icc x y) z 1 = 1 := by
  change _ = one_tangentSpace_Icc (Set.projIcc x y h.out.le z)
  simp [one_tangentSpace_Icc]
  congr
  simp only [projIcc_of_mem h.out.le hz]

lemma mfderiv_subtypeVal_Icc_one {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun (z : Icc x y) ↦ (z : ℝ)) z 1 = 1 := by
  have A : Set.EqOn (Subtype.val ∘ (Set.projIcc x y h.out.le)) id (Icc x y) := by
    intro z hz
    simp [projIcc_of_mem h.out.le hz]
  have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (Subtype.val ∘ (Set.projIcc x y h.out.le)) (Icc x y) z
      = mfderivWithin 𝓘(ℝ) 𝓘(ℝ) id (Icc x y) z := by
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
  sorry





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

instance : IsRiemannianManifold 𝓘(ℝ, F) F := by
  refine ⟨fun x y ↦ le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ



end
