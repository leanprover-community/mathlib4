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
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Manifold structure on real intervals

The manifold structure on real intervals is defined in `Mathlib.Geometry.Manifold.Instances.Real`.
We relate it to the manifold structure on the real line, by showing that the inclusion
(`contMDiff_subtype_coe_Icc`) and projection (`contMDiffOn_projIcc`) are smooth, and showing that
a function defined on the interval is smooth iff its composition with the projection is smooth on
the interval in `ℝ` (see `contMDiffOn_comp_projIcc_iff` and friends).

We also define `1 : TangentSpace (𝓡∂ 1) z`, and relate it to `1` in the real line.

- the inclusion `Icc x y → ℝ` is a smooth embedding, and in particular smooth

## TODO

This file can be thoroughly rewritten once mathlib has a good theory of smooth submersions.
Once this is done,
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

-- def bars : EuclideanSpace ℝ (Fin 1) → ℝ := fun z' ↦ (z' 0 : ℝ)

-- set_option backward.isDefEq.respectTransparency false in
-- def barz : ℝ → EuclideanSpace ℝ (Fin 1) := fun z' ↦ toLp 2 <| fun _ ↦ z'

-- TODO: name appropriately! and does/should this exist already?
def bar : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ where
  toFun := fun z' ↦ (z' 0 : ℝ)
  invFun := fun z ↦ toLp 2 <| fun _ ↦ z
  left_inv z := by ext; rw [← Fin.eq_zero _]
  map_add' := by intro; simp
  map_smul' := by intro; simp

@[simp]
lemma bar_apply (z : EuclideanSpace ℝ (Fin 1)) : bar z = z 0 := rfl

open Manifold IsManifold

-- TODO: all these lemmas are technically misnamed; the relevant coercion is Subtype.val!

set_option linter.flexible false in
-- TODO: the proof works, except that some details with the chosen computation are not right
/-- The inclusion map from a closed segment to `ℝ` is a smooth immersion -/
lemma isImmersionOfComplement_subtype_coe_Icc :
    IsImmersionOfComplement (EuclideanSpace ℝ (Fin 0)) (𝓡∂ 1) 𝓘(ℝ) ⊤
      (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  letI φ₀ := ContinuousLinearEquiv.prodUnique ℝ
    (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 0))
  let φ : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 0)) ≃L[ℝ] ℝ := φ₀.trans bar
  -- TODO: make convenience constructor with the charts being the default ones?
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) φ
    (chartAt (EuclideanHalfSpace 1) z) (chartAt ℝ (z : ℝ)) (mem_chart_source _ z)
    (mem_chart_source ..) (chart_mem_maximalAtlas _) (chart_mem_maximalAtlas _)
  intro z' hz'
  by_cases hz : ↑z < y
  · simp [hz, IccLeftChart, modelWithCornersEuclideanHalfSpace]
    simp [hz, IccLeftChart] at hz'
    have : 0 ≤ z' 0 := by
      obtain ⟨⟨y', hy'⟩, rfl⟩ := hz'.1
      simpa [modelWithCornersEuclideanHalfSpace]
    rw [min_eq_left, max_eq_left this]
    · simp [φ, φ₀, add_comm]
      sorry -- trouble: I need to pick a slightly different chart, to translate by x!
    · replace hz' := hz'.2
      simp [modelWithCornersEuclideanHalfSpace] at hz'
      rw [max_eq_left this]
      linarith
  · simp [hz, IccRightChart, modelWithCornersEuclideanHalfSpace]
    simp [hz, IccRightChart] at hz'
    have : 0 ≤ z' 0 := by
      obtain ⟨⟨y', hy'⟩, rfl⟩ := hz'.1
      simpa [modelWithCornersEuclideanHalfSpace]
    rw [max_eq_left, max_eq_left this]
    · simp [φ, φ₀]
      sorry -- trouble: I need to pick a slightly different chart, to translate by x!
    · replace hz' := hz'.2
      simp [modelWithCornersEuclideanHalfSpace] at hz'
      rw [max_eq_left this]
      linarith

/-- The inclusion map from a closed segment to `ℝ` is a smooth embedding -/
lemma isSmoothEmbedding_subtype_coe_Icc :
    IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ) ⊤ (fun (z : Icc x y) ↦ (z : ℝ)) :=
  ⟨isImmersionOfComplement_subtype_coe_Icc.isImmersion, Topology.IsEmbedding.subtypeVal⟩

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion map from of a closed segment to `ℝ` is smooth in the manifold sense. -/
lemma contMDiff_subtype_coe_Icc : CMDiff n (fun (z : Icc x y) ↦ (z : ℝ)) :=
  (isImmersionOfComplement_subtype_coe_Icc (x := x) (y := y)).contMDiff.of_le (OrderTop.le_top n)

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
  convert! hf.comp_contMDiff (contMDiff_subtype_coe_Icc (x := x) (y := y)) (fun z ↦ z.2)
  ext z
  simp

lemma contMDiffWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    CMDiffAt[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) w ↔ CMDiffAt n f w := by
  refine ⟨fun hf ↦ ?_,
    fun hf ↦ hf.comp_contMDiffWithinAt_of_eq (contMDiffOn_projIcc w w.2) (by simp)⟩
  have A := contMDiff_subtype_coe_Icc (x := x) (y := y) (n := n) w
  rw [← contMDiffWithinAt_univ] at A ⊢
  convert! hf.comp _ A (fun z hz ↦ z.2)
  ext z
  simp

lemma mdifferentiableWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    MDiffAt[Icc x y] (f ∘ (Set.projIcc x y h.out.le)) w ↔ MDiffAt f w := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have A := (contMDiff_subtype_coe_Icc (x := x) (y := y) w).mdifferentiableAt one_ne_zero
    rw [← mdifferentiableWithinAt_univ] at A ⊢
    convert! hf.comp _ A (fun z hz ↦ z.2)
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
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have : w = projIcc x y h.out.le (w : ℝ) := by rw [projIcc_of_mem]
  rw [projIcc_of_mem _ w.2]
  congr 1
  convert! mfderivWithin_projIcc_one w.2

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
