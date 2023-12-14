/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Convex.Normed

#align_import geometry.manifold.vector_bundle.tangent from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-! # Tangent bundles

This file defines the tangent bundle as a smooth vector bundle.

Let `M` be a smooth manifold with corners with model `I` on `(E, H)`. We define the tangent bundle
of `M` using the `VectorBundleCore` construction indexed by the charts of `M` with fibers `E`.
Given two charts `i, j : PartialHomeomorph M H`, the coordinate change between `i` and `j`
at a point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a smooth vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions

* `TangentSpace I M x` is the fiber of the tangent bundle at `x : M`, which is defined to be `E`.

* `TangentBundle I M` is the total space of `TangentSpace I M`, proven to be a smooth vector
  bundle.
-/


open Bundle Set SmoothManifoldWithCorners PartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (I)

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  smooth on its source. -/
theorem contDiffOn_fderiv_coord_change (i j : atlas H M) :
    ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I := by
    rw [i.1.extend_coord_change_source]; apply image_subset_range
  intro x hx
  refine' (ContDiffWithinAt.fderivWithin_right _ I.unique_diff le_top <| h hx).mono h
  refine' (PartialHomeomorph.contDiffOn_extend_coord_change I (subset_maximalAtlas I j.2)
    (subset_maximalAtlas I i.2) x hx).mono_of_mem _
  exact i.1.extend_coord_change_source_mem_nhdsWithin j.1 I hx
#align cont_diff_on_fderiv_coord_change contDiffOn_fderiv_coord_change

variable (M)

open SmoothManifoldWithCorners

/-- Let `M` be a smooth manifold with corners with model `I` on `(E, H)`.
Then `VectorBundleCore I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
@[simps indexAt coordChange]
def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    simp only
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_id', ContinuousLinearMap.id_apply]
    · exact I.unique_diff_at_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin I hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hx]
  continuousOn_coordChange i j := by
    refine' (contDiffOn_fderiv_coord_change I i j).continuousOn.comp
      ((i.1.continuousOn_extend I).mono _) _
    · rw [i.1.extend_source]; exact inter_subset_left _ _
    simp_rw [← i.1.extend_image_source_inter, mapsTo_image]
  coordChange_comp := by
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds I hxi (j.1.extend_source_mem_nhds I hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hxi, j.1.extend_left_inv I hxj]
    · exact (contDiffWithinAt_extend_coord_change' I (subset_maximalAtlas I k.2)
        (subset_maximalAtlas I j.2) hxk hxj).differentiableWithinAt le_top
    · exact (contDiffWithinAt_extend_coord_change' I (subset_maximalAtlas I j.2)
        (subset_maximalAtlas I i.2) hxj hxi).differentiableWithinAt le_top
    · intro x _; exact mem_range_self _
    · exact I.unique_diff_at_image
    · rw [Function.comp_apply, i.1.extend_left_inv I hxi]
#align tangent_bundle_core tangentBundleCore

-- porting note: moved to a separate `simp high` lemma b/c `simp` can simplify the LHS
@[simp high]
theorem tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.source := rfl

variable {M}

theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl
#align tangent_bundle_core_coord_change_achart tangentBundleCore_coordChange_achart

section tangentCoordChange

/-- Since `tangentBundleCore` has the same base sets as the preferred charts of the base manifold,
  we define `tangentCoordChange I x y` as a convenient abbreviation for a change of coordinates
  between the preferred charts at `x y : M`. -/
abbrev tangentCoordChange (x y : M) := (tangentBundleCore I M).coordChange (achart H x) (achart H y)

variable {I}

lemma tangentCoordChange_def {x y z : M} : tangentCoordChange I x y z =
    fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) := rfl

lemma tangentCoordChange_self {x z : M} {v : E} (h : z ∈ (extChartAt I x).source) :
    tangentCoordChange I x x z v = v := by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

lemma tangentCoordChange_comp {w x y z : M} {v : E}
    (h : z ∈ (extChartAt I w).source ∩ (extChartAt I x).source ∩ (extChartAt I y).source) :
    tangentCoordChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v := by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

lemma hasFDerivWithinAt_tangentCoordChange {x y z : M}
    (h : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) :
    HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I x).symm) (tangentCoordChange I x y z)
      (range I) (extChartAt I x z) :=
  have h' : extChartAt I x z ∈ ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change I y x h').differentiableWithinAt (by simp)).hasFDerivWithinAt

lemma continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChange I x y)
    ((extChartAt I x).source ∩ (extChartAt I y).source) := by
  convert (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

end tangentCoordChange

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangentBundleCore I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unusedArguments]
def TangentSpace {𝕜} [NontriviallyNormedField 𝕜] {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M} [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] (_x : M) : Type* := E
-- porting note: was deriving TopologicalSpace, AddCommGroup, TopologicalAddGroup
#align tangent_space TangentSpace

instance {x : M} : TopologicalSpace (TangentSpace I x) := inferInstanceAs (TopologicalSpace E)
instance {x : M} : AddCommGroup (TangentSpace I x) := inferInstanceAs (AddCommGroup E)
instance {x : M} : TopologicalAddGroup (TangentSpace I x) := inferInstanceAs (TopologicalAddGroup E)

variable (M)

-- is empty if the base manifold is empty
/-- The tangent bundle to a smooth manifold, as a Sigma type. Defined in terms of
`Bundle.TotalSpace` to be able to put a suitable topology on it. -/
@[reducible] -- porting note: was nolint has_nonempty_instance
def TangentBundle :=
  Bundle.TotalSpace E (TangentSpace I : M → Type _)
#align tangent_bundle TangentBundle

local notation "TM" => TangentBundle I M

section TangentBundleInstances

/- In general, the definition of tangent_space is not reducible, so that type class inference
does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/
section

variable {M} (x : M)

instance : Module 𝕜 (TangentSpace I x) := inferInstanceAs (Module 𝕜 E)

instance : Inhabited (TangentSpace I x) := ⟨0⟩

-- porting note: removed unneeded ContinuousAdd (TangentSpace I x)

end

instance : TopologicalSpace TM :=
  (tangentBundleCore I M).toTopologicalSpace

instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).fiberBundle

instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).vectorBundle

namespace TangentBundle

protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).toFiberBundleCore.localTriv (achart H p.1)).toPartialHomeomorph ≫ₕ
        (chartAt H p.1).prod (PartialHomeomorph.refl E) :=
  rfl
#align tangent_bundle.chart_at TangentBundle.chartAt

theorem chartAt_toPartialEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsPartialEquiv (achart H p.1) ≫
        (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E) :=
  rfl
#align tangent_bundle.chart_at_to_local_equiv TangentBundle.chartAt_toPartialEquiv

theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl
#align tangent_bundle.trivialization_at_eq_local_triv TangentBundle.trivializationAt_eq_localTriv

@[simp, mfld_simps]
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl
#align tangent_bundle.trivialization_at_source TangentBundle.trivializationAt_source

@[simp, mfld_simps]
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl
#align tangent_bundle.trivialization_at_target TangentBundle.trivializationAt_target

@[simp, mfld_simps]
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl
#align tangent_bundle.trivialization_at_base_set TangentBundle.trivializationAt_baseSet

theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) z.2) :=
  rfl
#align tangent_bundle.trivialization_at_apply TangentBundle.trivializationAt_apply

@[simp, mfld_simps]
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl
#align tangent_bundle.trivialization_at_fst TangentBundle.trivializationAt_fst

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : TM) :
    p ∈ (chartAt (ModelProd H E) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
#align tangent_bundle.mem_chart_source_iff TangentBundle.mem_chart_source_iff

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p ∈ (chartAt (ModelProd H E) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  /- porting note: was
  simp (config := { contextual := true }) only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp (config := { contextual := true }) only [and_iff_left_iff_imp, mfld_simps]
#align tangent_bundle.mem_chart_target_iff TangentBundle.mem_chart_target_iff

@[simp, mfld_simps]
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl
#align tangent_bundle.coe_chart_at_fst TangentBundle.coe_chartAt_fst

@[simp, mfld_simps]
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl
#align tangent_bundle.coe_chart_at_symm_fst TangentBundle.coe_chartAt_symm_fst

@[simp, mfld_simps]
theorem trivializationAt_continuousLinearMapAt {b₀ b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b :=
  (tangentBundleCore I M).localTriv_continuousLinearMapAt hb
#align tangent_bundle.trivialization_at_continuous_linear_map_at TangentBundle.trivializationAt_continuousLinearMapAt

@[simp, mfld_simps]
theorem trivializationAt_symmL {b₀ b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b :=
  (tangentBundleCore I M).localTriv_symmL hb
set_option linter.uppercaseLean3 false in
#align tangent_bundle.trivialization_at_symmL TangentBundle.trivializationAt_symmL

-- porting note: `simp` simplifies LHS to `.id _ _`
@[simp high, mfld_simps]
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using
    fderivWithin_id uniqueDiffWithinAt_univ
#align tangent_bundle.coord_change_model_space TangentBundle.coordChange_model_space

-- porting note: `simp` simplifies LHS to `.id _ _`
@[simp high, mfld_simps]
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.trivializationAt_symmL, coordChange_model_space]
  apply mem_univ
set_option linter.uppercaseLean3 false in
#align tangent_bundle.symmL_model_space TangentBundle.symmL_model_space

-- porting note: `simp` simplifies LHS to `.id _ _`
@[simp high, mfld_simps]
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.trivializationAt_continuousLinearMapAt, coordChange_model_space]
  apply mem_univ
#align tangent_bundle.continuous_linear_map_at_model_space TangentBundle.continuousLinearMapAt_model_space

end TangentBundle

instance tangentBundleCore.isSmooth : (tangentBundleCore I M).IsSmooth I := by
  refine' ⟨fun i j => _⟩
  rw [SmoothOn, contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas I i.2),
    contMDiffOn_iff_contDiffOn]
  refine' ((contDiffOn_fderiv_coord_change I i j).congr fun x hx => _).mono _
  · rw [PartialEquiv.trans_source'] at hx
    simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
  · exact (i.1.extend_image_source_inter j.1 I).subset
  · apply inter_subset_left
#align tangent_bundle_core.is_smooth tangentBundleCore.isSmooth

instance TangentBundle.smoothVectorBundle : SmoothVectorBundle E (TangentSpace I : M → Type _) I :=
  (tangentBundleCore I M).smoothVectorBundle _
#align tangent_bundle.smooth_vector_bundle TangentBundle.smoothVectorBundle

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/


/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `TotalSpace.toProd`. -/
@[simp, mfld_simps]
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.toProd H E).toPartialEquiv := by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · -- porting note: was ext; · rfl; apply hEq_of_eq
    refine congr_arg (TotalSpace.mk _) ?_
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv,
    FiberBundleCore.localTrivAsPartialEquiv, VectorBundleCore.toFiberBundleCore_baseSet,
    tangentBundleCore_baseSet]
  simp only [mfld_simps]
#align tangent_bundle_model_space_chart_at tangentBundle_model_space_chartAt

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = TotalSpace.toProd H E := by
  rw [← PartialHomeomorph.coe_coe, tangentBundle_model_space_chartAt]; rfl
#align tangent_bundle_model_space_coe_chart_at tangentBundle_model_space_coe_chartAt

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm := by
  rw [← PartialHomeomorph.coe_coe, PartialHomeomorph.symm_toPartialEquiv,
    tangentBundle_model_space_chartAt]; rfl
#align tangent_bundle_model_space_coe_chart_at_symm tangentBundle_model_space_coe_chartAt_symm

theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z = ContinuousLinearMap.id 𝕜 E :=
  by ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v
#align tangent_bundle_core_coord_change_model_space tangentBundleCore_coordChange_model_space

variable (H)

/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [continuous_iff_continuousOn_univ]
        convert (chartAt (ModelProd H E) p).continuousOn
        simp only [TangentSpace.fiberBundle, mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [continuous_iff_continuousOn_univ]
        convert (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }
#align tangent_bundle_model_space_homeomorph tangentBundleModelSpaceHomeomorph

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph H I : TangentBundle I H → ModelProd H E) =
      TotalSpace.toProd H E :=
  rfl
#align tangent_bundle_model_space_homeomorph_coe tangentBundleModelSpaceHomeomorph_coe

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph H I).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm :=
  rfl
#align tangent_bundle_model_space_homeomorph_coe_symm tangentBundleModelSpaceHomeomorph_coe_symm

section inTangentCoordinates

variable (I') {M H} {N : Type*}

/-- The map `in_coordinates` for the tangent bundle is trivial on the model spaces -/
theorem inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ = ϕ := by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
#align in_coordinates_tangent_bundle_core_model_space inCoordinates_tangent_bundle_core_model_space

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
in charts around `g x`, `inTangentCoordinates I I' f g ϕ x₀ x` is a coordinate change of
this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
by composing it with appropriate coordinate changes.
Note that the type of `ϕ` is more accurately
`Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)`.
We are unfolding `TangentSpace` in this type so that Lean recognizes that the type of `ϕ` doesn't
actually depend on `f` or `g`.

This is the underlying function of the trivializations of the hom of (pullbacks of) tangent spaces.
-/
def inTangentCoordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)
#align in_tangent_coordinates inTangentCoordinates

theorem inTangentCoordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    inTangentCoordinates I I' f g ϕ x₀ = ϕ := by
  simp (config := { unfoldPartialApp := true }) only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space]
#align in_tangent_coordinates_model_space inTangentCoordinates_model_space

theorem inTangentCoordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (tangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L
        ϕ x ∘L (tangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x) :=
  (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy
#align in_tangent_coordinates_eq inTangentCoordinates_eq

end inTangentCoordinates

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

instance {x : M} : PathConnectedSpace (TangentSpace I x) := by unfold TangentSpace; infer_instance

end Real
