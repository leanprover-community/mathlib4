/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Convert orthogonal smooth `M → 𝕊ⁿ` & `M → ℝⁿ⁺¹` to smooth `M → T𝕊ⁿ`

## Main definitions

* `sphereTangentMap` : Convert `f : M → 𝕊ⁿ` & `g : M → ℝⁿ⁺¹` which satisfy `∀ x, ⟪f x, g x⟫_ℝ = 0`
  to `M → T𝕊ⁿ`.

## Main statements

* `mfderiv_coe_sphere_sphereTangentMap_snd` : Let `ι` be an inclusion map from `T𝕊ⁿ` to `Tℝⁿ⁺¹`,
  then `ι (sphereTangentMap n f g hf x).snd = g x`.

* `contMDiff_sphereTangentMap` : If `f` & `g` are smooth, then `sphereTangentMap n f g hf'` too.

-/

open Metric Module Function

open scoped Manifold ContDiff InnerProductSpace

open private stereographic'_neg from Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E)
variable {m : WithTop ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

/-- Convert `f : M → 𝕊ⁿ` & `g : M → ℝⁿ⁺¹` which satisfy `∀ x, ⟪f x, g x⟫_ℝ = 0` to `M → T𝕊ⁿ`. -/
def sphereTangentMap (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (f : M → sphere (0 : E) 1) (g : M → E)
    (hf : ∀ x, ⟪(↑(f x) : E), g x⟫_ℝ = 0) (x : M) : TangentBundle (𝓡 n) (sphere (0 : E) 1) :=
  ⟨f x,
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-f x))).repr
      (⟨g x, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by simp [hf x])⟩ :
        (ℝ ∙ (-↑(f x) : E))ᗮ)⟩

omit [TopologicalSpace M] in
@[simp]
theorem sphereTangentMap_proj (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (f : M → sphere (0 : E) 1) (g : M → E)
    (hf : ∀ x, ⟪(↑(f x) : E), g x⟫_ℝ = 0) (x : M) : (sphereTangentMap n f g hf x).proj = f x :=
  rfl

omit [TopologicalSpace M] in
/-- Let `ι` be an inclusion map from `T𝕊ⁿ` to `Tℝⁿ⁺¹`, then
`ι (sphereTangentMap n f g hf x).snd = g x`. -/
@[simp]
theorem mfderiv_coe_sphere_sphereTangentMap_snd (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (f : M → sphere (0 : E) 1) (g : M → E)
    (hf : ∀ x, ⟪(↑(f x) : E), g x⟫_ℝ = 0) (x : M) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (f x) (sphereTangentMap n f g hf x).snd =
      g x := by
  rw [((contMDiff_coe_sphere (f x)).mdifferentiableAt le_top).mfderiv]
  simp only [writtenInExtChartAt, extChartAt, PartialHomeomorph.extend,
    PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
    PartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, PartialEquiv.refl_coe, PartialHomeomorph.coe_coe_symm,
    CompTriple.comp_eq, modelWithCornersSelf_coe, Set.range_id, PartialHomeomorph.toFun_eq_coe,
    chartAt, ChartedSpace.chartAt, stereographic'_neg, fderivWithin_univ]
  simp only [chartAt, ChartedSpace.chartAt, stereographic', coe_neg_sphere, stereographic,
    PartialHomeomorph.coe_trans_symm, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk,
    Homeomorph.toPartialHomeomorph_symm_apply, LinearIsometryEquiv.toHomeomorph_symm,
    LinearIsometryEquiv.coe_toHomeomorph, ← comp_assoc, coe_sphere_comp_stereoInvFun]
  simp only [comp_assoc]
  conv =>
    enter [1, 1]
    tactic =>
      rw [fderiv_comp]
      · exact contDiff_stereoInvFunAux.contDiffAt.differentiableAt (right_eq_inf.mp rfl)
      · exact
          (((ℝ ∙ (-↑(f x) : E))ᗮ).subtypeL.comp
            (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := E) n
              (ne_zero_of_mem_unit_sphere (-f x))
            ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).differentiableAt
  conv =>
    enter [1, 1, 2]
    exact
      (((ℝ ∙ (-↑(f x) : E))ᗮ).subtypeL.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := E) n
            (ne_zero_of_mem_unit_sphere (-f x))
          ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).fderiv
  simp [sphereTangentMap, TangentSpace, (hasFDerivAt_stereoInvFunAux (-(↑(f x) : E))).fderiv]

omit [IsManifold I m M] in
private theorem contMDiff_sphereTangentMap_aux {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → ↥(sphere (0 : E) 1)} {g : M → E}
    (hf : ContMDiff I (𝓡 n) m f) (hf' : ∀ x, ⟪(↑(f x) : E), g x⟫_ℝ = 0)
    (hg : ContMDiff I 𝓘(ℝ, E) m g) (p : ↥(sphere (0 : E) 1)) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m
      (fun x =>
        (fderiv ℝ
            (⇑(chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
              ⇑(chartAt (EuclideanSpace ℝ (Fin n)) (f x)).symm) 0)
          (sphereTangentMap n f g hf' x).snd)
      (f ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) p).source) := by
  conv =>
    enter [4, x, 1, 2]
    change ⇑(stereographic' n (-p)) ∘ ⇑(stereographic' n (-f x)).symm
    simp only [stereographic', coe_neg_sphere, stereographic,
      PartialHomeomorph.coe_trans, Homeomorph.toPartialHomeomorph_apply,
      LinearIsometryEquiv.coe_toHomeomorph, PartialHomeomorph.mk_coe,
      PartialHomeomorph.coe_trans_symm, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk,
      Homeomorph.toPartialHomeomorph_symm_apply, LinearIsometryEquiv.toHomeomorph_symm,
      comp_assoc]
    simp only [← comp_assoc Subtype.val, coe_sphere_comp_stereoInvFun]
    simp only [← comp_assoc]
    simp only [comp_assoc _ Subtype.val, comp_assoc _ (stereoToFun (-(↑p : E)))]
  conv =>
    tactic =>
      apply propext ∘ contMDiffOn_congr
      intro x hx
      rw [fderiv_comp]
      · refine
          (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := E) n
            (ne_zero_of_mem_unit_sphere (-p))
          ).repr.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp _
            (DifferentiableAt.comp _ ?_
              (contDiff_stereoInvFunAux.contDiffAt.differentiableAt (right_eq_inf.mp rfl)))
        simp only [coe_neg_sphere, comp_apply, map_zero, ZeroMemClass.coe_zero,
          stereoInvFunAux_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, zero_add, smul_zero, zero_sub, smul_neg, neg_smul, neg_neg, inv_smul_smul₀]
        refine
          ((contDiffOn_stereoToFun (E := E) (v := -(↑p : E))).contDiffAt (IsOpen.mem_nhds ?_ ?_)
            ).differentiableAt (right_eq_inf.mp rfl)
        · exact
            (innerSL ℝ (-(↑p : E))).continuous.isOpen_preimage {1}ᶜ isOpen_compl_singleton
        · simp only [innerSL_apply, ne_eq, Set.mem_setOf_eq, ← sphere_ext_iff, ← coe_neg_sphere]
          simpa [chartAt, ChartedSpace.chartAt, eq_comm (a := f x)] using hx
      · exact
          (((ℝ ∙ (-↑(f x) : E))ᗮ).subtypeL.comp
            (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := E) n
              (ne_zero_of_mem_unit_sphere (-f x))
            ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).differentiableAt
  conv =>
    enter [4, x, 1, 2]
    exact
      (((ℝ ∙ (-↑(f x) : E))ᗮ).subtypeL.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := E) n
            (ne_zero_of_mem_unit_sphere (-f x))
          ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).fderiv
  simp only [comp_apply, map_zero, ZeroMemClass.coe_zero, coe_neg_sphere, sphereTangentMap,
    ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL', Submodule.coe_subtype,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply]
  refine ContMDiffOn.clm_apply (fun x hx => ContMDiffAt.contMDiffWithinAt ?_) hg.contMDiffOn
  conv =>
    arg 4
    change
      (fun x => fderiv ℝ ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ∘ stereoToFun (-(↑p : E)) ∘
          stereoInvFunAux (-x)) 0) ∘ ((↑) : ↥(sphere (0 : E) 1) → E) ∘ f
  refine
    ContMDiffAt.comp _ (ContMDiffAt.of_le ?_ le_top)
      (((contMDiff_coe_sphere (E := E) (n := n)).contMDiffAt.of_le le_top).comp _
        hf.contMDiffAt)
  rw [contMDiffAt_iff_contDiffAt]
  refine ContDiffAt.fderiv (n := ω) ?_ contDiffAt_const (right_eq_inf.mp rfl)
  conv =>
    arg 3
    change
      (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr ∘
        (stereoToFun (-(↑p : E)) ∘ uncurry stereoInvFunAux) ∘ Prod.map Neg.neg id
  refine
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := E) n
        (ne_zero_of_mem_unit_sphere (-p))
      ).repr.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp _ ?_
  refine ContDiffAt.comp _ ?_ (ContDiffAt.prod_map contDiff_neg.contDiffAt contDiffAt_id)
  refine ContDiffAt.comp _ ?_ contDiff_uncurry_stereoInvFunAux.contDiffAt
  simp only [coe_neg_sphere, comp_apply, Prod.map_apply, id_eq, uncurry_apply_pair,
    stereoInvFunAux_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add, smul_zero, zero_sub, smul_neg, neg_smul, neg_neg, inv_smul_smul₀]
  refine
    (contDiffOn_stereoToFun (E := E) (v := -(↑p : E))).contDiffAt (IsOpen.mem_nhds ?_ ?_)
  · exact
      (innerSL ℝ (-(↑p : E))).continuous.isOpen_preimage {1}ᶜ isOpen_compl_singleton
  · simp only [map_neg, ContinuousLinearMap.neg_apply, innerSL_apply, ne_eq,
      Set.mem_setOf_eq]
    have hp := inner_eq_norm_mul_iff_real (x := (↑p : E)) (y := -(↑(f x) : E))
    simp only [inner_neg_right, norm_eq_of_mem_sphere, norm_neg, mul_one, one_smul,
      smul_neg, chartAt, ChartedSpace.chartAt, stereographic'_source, Set.mem_compl_iff,
      Set.mem_singleton_iff] at hp hx
    rw [hp, ← coe_neg_sphere, Subtype.val_inj, ← neg_eq_iff_eq_neg, ← ne_eq]
    symm; exact hx

/-- If `f` & `g` are smooth, then `sphereTangentMap n f g hf'` too. -/
theorem contMDiff_sphereTangentMap {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → ↥(sphere (0 : E) 1)} {g : M → E}
    (hf : ContMDiff I (𝓡 n) m f) (hf' : ∀ x, ⟪(↑(f x) : E), g x⟫_ℝ = 0)
    (hg : ContMDiff I 𝓘(ℝ, E) m g) : ContMDiff I (𝓡 n).tangent m (sphereTangentMap n f g hf') := by
  rw [contMDiff_iff_target]
  constructor
  · rw [continuous_generateFrom_iff]
    simp only [FiberBundleCore.localTrivAsPartialEquiv_source, FiberBundleCore.proj,
      FiberBundleCore.localTrivAsPartialEquiv_coe, Set.iUnion_coe_set, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop, forall_exists_index, and_imp]
    rintro _ _ ⟨p, rfl⟩ s hs rfl; rcases neg_surjective p with ⟨p, rfl⟩
    rw [Set.preimage_inter]
    conv =>
      enter [1, 1]
      change
        sphereTangentMap n f g hf' ⁻¹'
          (Bundle.TotalSpace.proj ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    simp only [stereographic'_source, Set.preimage_compl, Set.preimage_preimage,
      sphereTangentMap_proj, FiberBundleCore.localTriv_apply,
      VectorBundleCore.toFiberBundleCore_indexAt, tangentBundleCore_indexAt,
      VectorBundleCore.coe_coordChange, tangentBundleCore_coordChange, PartialHomeomorph.extend,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
      coe_achart, PartialHomeomorph.coe_coe_symm, modelWithCornersSelf_coe, Set.range_id,
      fderivWithin_univ]
    refine
      ContinuousOn.isOpen_inter_preimage (ContinuousOn.prod (contMDiff_iff.mp hf).1.continuousOn ?_)
        ((contMDiff_iff.mp hf).1.isOpen_preimage _
          (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source) hs
    simp only [chartAt, ChartedSpace.chartAt, stereographic'_neg]
    exact (contMDiffOn_iff.mp (contMDiff_sphereTangentMap_aux hf hf' hg p)).1
  · rintro ⟨p, v⟩
    conv =>
      arg 4
      simp only [extChartAt, PartialHomeomorph.extend, TangentBundle.chartAt,
        FiberBundleCore.proj, ← TangentBundle.trivializationAt_eq_localTriv,
        PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.prod_toPartialEquiv,
        PartialHomeomorph.refl_partialEquiv, modelWithCorners_prod_toPartialEquiv,
        modelWithCornersSelf_partialEquiv, PartialEquiv.refl_prod_refl, PartialEquiv.coe_trans,
        PartialEquiv.refl_coe, PartialEquiv.prod_coe, PartialHomeomorph.toFun_eq_coe, id_eq,
        Trivialization.coe_coe, comp_def, TangentBundle.trivializationAt_apply,
        PartialEquiv.trans_refl, PartialHomeomorph.coe_coe_symm, modelWithCornersSelf_coe,
        Set.range_id, fderivWithin_univ, CompTriple.comp_eq, sphereTangentMap_proj,
        chartAt, ChartedSpace.chartAt, stereographic'_neg]
    conv =>
      arg 5
      tactic =>
        ext x
        simp only [extChartAt, PartialHomeomorph.extend, modelWithCorners_prod_toPartialEquiv,
          modelWithCornersSelf_partialEquiv, PartialEquiv.refl_prod_refl, PartialEquiv.trans_source,
          PartialHomeomorph.toFun_eq_coe, PartialEquiv.refl_source, Set.preimage_univ,
          Set.inter_univ, Set.mem_preimage, TangentBundle.mem_chart_source_iff,
          sphereTangentMap_proj]
        rw [← Set.mem_preimage]
    apply ContMDiffOn.prod_mk_space
    · rw [contMDiff_iff_target] at hf
      simpa using hf.2 p
    · exact contMDiff_sphereTangentMap_aux hf hf' hg p
