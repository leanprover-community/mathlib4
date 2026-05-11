/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Manifold structure on real intervals

The manifold structure on real intervals is defined in `Mathlib.Geometry.Manifold.Instances.Real`.
We relate it to the manifold structure on the real line, by showing that the inclusion
(`contMDiff_subtype_coe_Icc`) and projection (`contMDiffOn_projIcc`) are smooth, and showing that
a function defined on the interval is smooth iff its composition with the projection is smooth on
the interval in `ℝ` (see `contMDiffOn_comp_projIcc_iff` and friends).

We also define `1 : TangentSpace (𝓡∂ 1) z`, and relate it to `1` in the real line.

## TODO

This file can be thoroughly rewritten once mathlib has a good theory of smooth immersions and
embeddings. Once this is done,
- the inclusion `Icc x y → ℝ` is a smooth embedding, and in particular smooth
- deduce the dual result: a function `f : M → Icc x y` is smooth iff
  its composition with the inclusion into `ℝ` is smooth
- prove the projection `ℝ → Icc x y` is a smooth submersion, hence smooth
- use this to simplify the proof that `f : Icc x y → M` is smooth iff the composition `ℝ → M`
  with the projection `ℝ → Icc x y` is
-/

@[expose] public section

open Set WithLp
open scoped Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance (x : ℝ) : One (TangentSpace 𝓘(ℝ) x) where
  one := (1 : ℝ)

/-- Unit vector in the tangent space to a segment, as the image of the unit vector in the real line
under the canonical projection. It is also mapped to the unit vector in the real line through
the canonical injection, see `mfderiv_subtype_coe_Icc_one`.

Note that one cannot abuse defeqs for this definition: this is *not* the same as the vector
`fun _ ↦ 1` in `EuclideanSpace ℝ (Fin 1)` through defeqs, as one of the charts of `Icc x y` is
orientation-reversing. -/
irreducible_def oneTangentSpaceIcc {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    TangentSpace (𝓡∂ 1) z :=
  mfderiv[Icc x y] (Set.projIcc x y h.out.le) z 1

instance {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) : One (TangentSpace (𝓡∂ 1) z) where
  one := oneTangentSpaceIcc z

variable {x y : ℝ} [h : Fact (x < y)] {n : WithTop ℕ∞}

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion map from of a closed segment to `ℝ` is smooth in the manifold sense. -/
lemma contMDiff_subtype_coe_Icc : CMDiff n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨by fun_prop, ?_⟩
  -- We come back to the definition: we should check that, in each chart, the map is smooth.
  -- There are two charts, and we check things separately in each of them using the
  -- explicit formulas.
  suffices ContDiffWithinAt ℝ n _ (range ↑(𝓡∂ 1)) _ by simpa
  split_ifs with hz
  · simp? [IccLeftChart, Function.comp_def, modelWithCornersEuclideanHalfSpace] says
      simp only [IccLeftChart, Fin.isValue, OpenPartialHomeomorph.mk_coe_symm,
        PartialEquiv.coe_symm_mk, modelWithCornersEuclideanHalfSpace, ModelWithCorners.mk_symm,
        Function.comp_def, Function.update_self, ModelWithCorners.mk_coe,
        OpenPartialHomeomorph.mk_coe]
    rw [Subtype.range_val_subtype]
    have : ContDiff ℝ n (fun (z : EuclideanSpace ℝ (Fin 1)) ↦ z 0 + x) := by fun_prop
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem; swap
    · simpa using z.2.1
    have : {w : EuclideanSpace ℝ (Fin 1) | w 0 < y - x} ∈ 𝓝 (toLp 2 fun i ↦ z - x) := by
      apply (isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const).mem_nhds
      simpa using hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with w hw h'w
    rw [max_eq_left hw, min_eq_left]
    linarith
  · simp only [not_lt] at hz
    simp? [IccRightChart, Function.comp_def, modelWithCornersEuclideanHalfSpace] says
      simp only [IccRightChart, Fin.isValue, OpenPartialHomeomorph.mk_coe_symm,
        PartialEquiv.coe_symm_mk, modelWithCornersEuclideanHalfSpace, ModelWithCorners.mk_symm,
        Function.comp_def, Function.update_self, ModelWithCorners.mk_coe,
        OpenPartialHomeomorph.mk_coe]
    rw [Subtype.range_val_subtype]
    have : ContDiff ℝ n (fun (z : EuclideanSpace ℝ (Fin 1)) ↦ y - z 0) := by fun_prop
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem; swap
    · simpa using z.2.2
    have : {w : EuclideanSpace ℝ (Fin 1) | w 0 < y - x} ∈ 𝓝 (toLp 2 fun i ↦ y - z) := by
      apply (isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const).mem_nhds
      simpa using h.out.trans_le hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with w hw h'w
    rw [max_eq_left hw, max_eq_left]
    linarith

/-- The projection from `ℝ` to a closed segment is smooth on the segment, in the manifold sense. -/
lemma contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIcc x y h.out.le) := by
  intro z hz
  rw [contMDiffWithinAt_iff]
  refine ⟨by apply ContinuousAt.continuousWithinAt; fun_prop, ?_⟩
  -- We come back to the definition: we should check that, in each chart, the map is smooth
  -- There are two charts, and we check things separately in each of them using the
  -- explicit formulas.
  suffices ContDiffWithinAt ℝ n _ (Icc x y) z by simpa
  split_ifs with h'z
  · have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from toLp 2 fun (_ : Fin 1) ↦ w - x)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    suffices max x (min y w) - x = w - x by
      simpa [modelWithCornersEuclideanHalfSpace, IccLeftChart]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]
  · have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from toLp 2 fun (_ : Fin 1) ↦ y - w)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    suffices y - max x (min y w) = y - w by
      simpa [modelWithCornersEuclideanHalfSpace, IccRightChart]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]

lemma contMDiffOn_comp_projIcc_iff {f : Icc x y → M} :
    CMDiff[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) ↔ CMDiff n f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp_contMDiffOn contMDiffOn_projIcc⟩
  convert hf.comp_contMDiff (contMDiff_subtype_coe_Icc (x := x) (y := y)) (fun z ↦ z.2)
  ext z
  simp

lemma contMDiffWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    CMDiffAt[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) w ↔ CMDiffAt n f w := by
  refine ⟨fun hf ↦ ?_,
    fun hf ↦ hf.comp_contMDiffWithinAt_of_eq (contMDiffOn_projIcc w w.2) (by simp)⟩
  have A := contMDiff_subtype_coe_Icc (x := x) (y := y) (n := n) w
  rw [← contMDiffWithinAt_univ] at A ⊢
  convert hf.comp _ A (fun z hz ↦ z.2)
  ext z
  simp

lemma mdifferentiableWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    MDiffAt[Icc x y] (f ∘ (Set.projIcc x y h.out.le)) w ↔ MDiffAt f w := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have A := (contMDiff_subtype_coe_Icc (x := x) (y := y) w).mdifferentiableAt one_ne_zero
    rw [← mdifferentiableWithinAt_univ] at A ⊢
    convert hf.comp _ A (fun z hz ↦ z.2)
    ext z
    simp
  · have := (contMDiffOn_projIcc (x := x) (y := y) w w.2).mdifferentiableWithinAt one_ne_zero
    exact MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq (w : ℝ) hf this (by simp)

lemma mfderivWithin_projIcc_one {z : ℝ} (hz : z ∈ Icc x y) :
    mfderiv[Icc x y] (Set.projIcc x y h.out.le) z 1 = 1 := by
  change _ = oneTangentSpaceIcc (Set.projIcc x y h.out.le z)
  simp only [oneTangentSpaceIcc]
  congr
  simp [projIcc_of_mem h.out.le hz]

set_option backward.isDefEq.respectTransparency false in
lemma mfderivWithin_comp_projIcc_one {f : Icc x y → M} {w : Icc x y} :
    mfderiv[Icc x y] (f ∘ (projIcc x y h.out.le)) w 1 = mfderiv% f w 1 := by
  by_cases hw : MDiffAt f w; swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hw, mfderivWithin_zero_of_not_mdifferentiableWithinAt]
    · rfl
    · rwa [mdifferentiableWithinAt_comp_projIcc_iff]
  rw [mfderiv_comp_mfderivWithin (I' := 𝓡∂ 1)]; rotate_left
  · simp [hw]
  · exact (contMDiffOn_projIcc _ w.2).mdifferentiableWithinAt one_ne_zero
  · exact (uniqueDiffOn_Icc h.out _ w.2).uniqueMDiffWithinAt
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
  have : w = projIcc x y h.out.le (w : ℝ) := by rw [projIcc_of_mem]
  rw [projIcc_of_mem _ w.2]
  congr 1
  convert mfderivWithin_projIcc_one w.2

lemma mfderiv_subtype_coe_Icc_one (z : Icc x y) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z 1 = 1 := by
  have A : mfderiv[Icc x y] (Subtype.val ∘ (projIcc x y h.out.le)) z 1
      = mfderiv[Icc x y] (@id ℝ) z 1 := by
    congr 1
    apply mfderivWithin_congr_of_mem _ z.2
    intro z hz
    simp [projIcc_of_mem h.out.le hz]
  rw [← mfderivWithin_comp_projIcc_one, A]
  simp only [id_eq, mfderivWithin_eq_fderivWithin]
  rw [fderivWithin_id (uniqueDiffOn_Icc h.out _ z.2)]
  rfl
