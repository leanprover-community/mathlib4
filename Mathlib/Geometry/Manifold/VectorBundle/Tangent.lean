/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Notation

/-! # Tangent bundles

This file defines the tangent bundle as a `C^n` vector bundle.

Let `M` be a manifold with model `I` on `(E, H)`. The tangent space `TangentSpace I (x : M)` has
already been defined as a type synonym for `E`, and the tangent bundle `TangentBundle I M` as an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

In this file, when `M` is `C^1`, we construct a vector bundle structure
on `TangentBundle I M` using the `VectorBundleCore` construction indexed by the charts of `M`
with fibers `E`. Given two charts `i, j : OpenPartialHomeomorph M H`, the coordinate change
between `i` and `j` at a point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions and results

* `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.

* When `M` is a `C^{n+1}` manifold, `TangentBundle I M` has a `C^n` vector bundle
  structure over `M`. In particular, it is a topological space, a vector bundle, a fiber bundle,
  and a `C^n` manifold.
-/

@[expose] public section


open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  `C^n` on its source. -/
theorem contDiffOn_fderiv_coord_change [IsManifold I (n + 1) M]
    (i j : atlas H M) :
    ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
    <| h hx).mono h
  refine (I.contDiffOn_extendCoordChange (subset_maximalAtlas i.2)
    (subset_maximalAtlas j.2) x hx).mono_of_mem_nhdsWithin ?_
  exact I.extendCoordChange_source_mem_nhdsWithin hx

open IsManifold

variable [IsManifold I 1 M] [IsManifold I' 1 M']

variable (I M) in
/-- Let `M` be a `C^1` manifold with model `I` on `(E, H)`.
Then `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.
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
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_id', ContinuousLinearMap.id_apply]
    · exact I.uniqueDiffWithinAt_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hx]
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + 1) M := by simpa
    refine (contDiffOn_fderiv_coord_change (n := 0) i j).continuousOn.comp
      (i.1.continuousOn_extend.mono ?_) ?_
    · rw [i.1.extend_source]; exact inter_subset_left
    exact mapsTo_iff_image_subset.2 (i.1.extend_image_source_inter j.1).subset
  coordChange_comp := by
    have : IsManifold I (0 + 1) M := by simpa
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds (I := I) hxi (j.1.extend_source_mem_nhds (I := I) hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hxi, j.1.extend_left_inv hxj]
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas j.2)
        (subset_maximalAtlas k.2) hxj hxk).differentiableWithinAt one_ne_zero
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas i.2)
        (subset_maximalAtlas j.2) hxi hxj).differentiableWithinAt one_ne_zero
    · intro x _; exact mem_range_self _
    · exact I.uniqueDiffWithinAt_image
    · rw [Function.comp_apply, i.1.extend_left_inv hxi]

/-- `simp`-normal form is `tangentBundleCore_localTriv_baseSet`. -/
theorem tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.source := rfl

@[simp]
theorem tangentBundleCore_localTriv_baseSet (i) :
    ((tangentBundleCore I M).localTriv i).baseSet = i.1.source := rfl

theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl

section tangentCoordChange

variable (I) in
/-- In a manifold `M`, given two preferred charts indexed by `x y : M`, `tangentCoordChange I x y`
is the family of derivatives of the corresponding change-of-coordinates map. It takes junk values
outside the intersection of the sources of the two charts.

Note that this definition takes advantage of the fact that `tangentBundleCore` has the same base
sets as the preferred charts of the base manifold. -/
abbrev tangentCoordChange (x y : M) : M → E →L[𝕜] E :=
  (tangentBundleCore I M).coordChange (achart H x) (achart H y)

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
  ((contDiffWithinAt_ext_coord_change y x h').differentiableWithinAt one_ne_zero).hasFDerivWithinAt

lemma continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChange I x y)
    ((extChartAt I x).source ∩ (extChartAt I y).source) := by
  convert (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

end tangentCoordChange

local notation "TM" => TangentBundle I M

section TangentBundleInstances

instance : TopologicalSpace TM :=
  inferInstanceAs <| TopologicalSpace (tangentBundleCore I M).TotalSpace

instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  inferInstanceAs <| FiberBundle E (tangentBundleCore I M).Fiber

instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  inferInstanceAs <| VectorBundle 𝕜 E (tangentBundleCore I M).Fiber

namespace TangentBundle

protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).toFiberBundleCore.localTriv
        (achart H p.1)).toOpenPartialHomeomorph ≫ₕ
        (chartAt H p.1).prod (OpenPartialHomeomorph.refl E) :=
  rfl

theorem chartAt_toPartialEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsPartialEquiv (achart H p.1) ≫
        (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E) :=
  rfl

theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl

theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) z.2) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : TM) :
    p ∈ (chartAt (ModelProd H E) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p ∈ (chartAt (ModelProd H E) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  /- porting note: was
  simp +contextual only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp +contextual only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of the tangent space can be expressed in terms of the tangent bundle core.
To write it as the manifold derivative of `extChartAt`, see
`TangentBundle.continuousLinearMapAt_trivializationAt`.

Use with care as it abuses the defeq `TangentSpace I b = E`. -/
theorem continuousLinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b := by
  simp [hb]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse trivialization of the tangent space can be expressed in terms of the tangent bundle
core. To write it as the manifold derivative of `(extChartAt I b₀).symm`, see
`TangentBundle.symmL_trivializationAt`.

Use with care as it abuses the defeq `TangentSpace I b = E`. -/
theorem symmL_trivializationAt_eq_core {b₀ b : M} (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b := by
  simp [hb]

/-! The lemmas below have high priority because `simp` simplifies the LHS to `.id _ _`;
we prefer `1` as the simp-normal form. -/
@[simp high, mfld_simps]
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using
    fderivWithin_id uniqueDiffWithinAt_univ

@[simp high, mfld_simps]
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core, coordChange_model_space]
  apply mem_univ

@[simp high, mfld_simps]
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core, coordChange_model_space]
  apply mem_univ

end TangentBundle

omit [IsManifold I 1 M] in
lemma tangentBundleCore.isContMDiff [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (tangentBundleCore I M).IsContMDiff I n := by
  have : IsManifold I n M := .of_le (n := n + 1) (le_self_add)
  refine ⟨fun i j => ?_⟩
  rw [contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas i.2),
    contMDiffOn_iff_contDiffOn]
  · refine ((contDiffOn_fderiv_coord_change (I := I) i j).congr fun x hx => ?_).mono ?_
    · rw [PartialEquiv.trans_source'] at hx
      simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
    · exact (i.1.extend_image_source_inter j.1).subset
  · apply inter_subset_left

omit [IsManifold I 1 M] in
lemma TangentBundle.contMDiffVectorBundle [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  exact (tangentBundleCore I M).instContMDiffVectorBundle

omit [IsManifold I 1 M] in
instance [h : IsManifold I ∞ M] :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
instance [IsManifold I ω M] :
    ContMDiffVectorBundle ω E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
instance [h : IsManifold I 2 M] :
    ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I := by
  have : IsManifold I (1 + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
theorem trivializationAt_model_space_apply (p : TangentBundle I H) (x : H) :
    trivializationAt E (TangentSpace I) x p = (p.1, p.2) := by
  simp only [TangentBundle.trivializationAt_apply]
  have : fderivWithin 𝕜 (↑I ∘ ↑I.symm) (range I) (I p.proj) =
      fderivWithin 𝕜 id (range I) (I p.proj) :=
    fderivWithin_congr' (fun y hy ↦ by simp [hy]) (mem_range_self p.proj)
  simp [this, fderivWithin_id (ModelWithCorners.uniqueDiffWithinAt_image I)]

set_option backward.isDefEq.respectTransparency false in
/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `TotalSpace.toProd`. -/
@[simp, mfld_simps]
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.toProd H E).toPartialEquiv := by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · ext; · rfl
    apply heq_of_eq
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv,
    FiberBundleCore.localTrivAsPartialEquiv, VectorBundleCore.toFiberBundleCore_baseSet,
    tangentBundleCore_baseSet]
  simp only [mfld_simps]

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = TotalSpace.toProd H E := by
  rw [← OpenPartialHomeomorph.coe_coe, tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm := by
  rw [← OpenPartialHomeomorph.coe_coe, OpenPartialHomeomorph.symm_toPartialEquiv,
    tangentBundle_model_space_chartAt]; rfl

theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z =
    ContinuousLinearMap.id 𝕜 E := by
  ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism. For the diffeomorphism version, see `tangentBundleModelSpaceDiffeomorph`. -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [← continuousOn_univ]
        convert (chartAt (ModelProd H E) p).continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [← continuousOn_univ]
        convert (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H → ModelProd H E) =
      TotalSpace.toProd H E :=
  rfl

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_tangentBundleModelSpaceHomeomorph :
    ContMDiff I.tangent (I.prod 𝓘(𝕜, E)) n
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H → ModelProd H E) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y ↦ ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_tangentBundleModelSpaceHomeomorph_symm :
    ContMDiff (I.prod 𝓘(𝕜, E)) I.tangent n
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E → TangentBundle I H) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y ↦ ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simpa [PartialEquiv.prod] using ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (H I) in
/-- In the tangent bundle to the model space, the second projection is `C^n`. -/
lemma contMDiff_snd_tangentBundle_modelSpace :
    ContMDiff I.tangent 𝓘(𝕜, E) n (fun (p : TangentBundle I H) ↦ p.2) := by
  change ContMDiff I.tangent 𝓘(𝕜, E) n
    ((id Prod.snd : ModelProd H E → E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} {x : E} :
    CMDiffAt[s] n (T% V) x ↔ ContDiffWithinAt 𝕜 n V s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ContMDiffWithinAt.contDiffWithinAt <|
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert h.contMDiffWithinAt with y
    simp

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiffAt_vectorSpace_iff_contDiffAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {x : E} :
    CMDiffAt n (T% V) x ↔ ContDiffAt 𝕜 n V x := by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiffOn_vectorSpace_iff_contDiffOn
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    CMDiff[s] n (T% V) ↔ ContDiffOn 𝕜 n V s := by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiff_vectorSpace_iff_contDiff {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} :
    CMDiff n (T% V) ↔ ContDiff 𝕜 n V := by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]

section inTangentCoordinates

variable {N : Type*}

/-- The map `inCoordinates` for the tangent bundle is trivial on the model spaces -/
theorem inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ = ϕ := by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

variable (I I') in
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

theorem inTangentCoordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    inTangentCoordinates I I' f g ϕ x₀ = ϕ := by
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space]

/-- To write a linear map between tangent spaces in coordinates amounts to precomposing and
postcomposing it with suitable coordinate changes. For a concrete version expressing the
change of coordinates as derivatives of extended charts,
see `inTangentCoordinates_eq_mfderiv_comp`. -/
theorem inTangentCoordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (tangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L
        ϕ x ∘L (tangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x) :=
  (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy

end inTangentCoordinates

end General
