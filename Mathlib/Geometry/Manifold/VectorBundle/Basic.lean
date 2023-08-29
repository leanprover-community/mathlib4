/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear
import Mathlib.Topology.VectorBundle.Constructions

#align_import geometry.manifold.vector_bundle.basic from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-! # Smooth vector bundles

This file defines smooth vector bundles over a smooth manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`.  We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`.

Now, we define `SmoothVectorBundle` as the `Prop` of having smooth transition functions.
Recall the structure groupoid `smoothFiberwiseLinear` on `B × F` consisting of smooth, fiberwise
linear local homeomorphisms.  We show that our definition of "smooth vector bundle" implies
`HasGroupoid` for this groupoid, and show (by a "composition" of `HasGroupoid` instances) that
this means that a smooth vector bundle is a smooth manifold.

Since `SmoothVectorBundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be smooth vector bundles over several different base
fields, they can also be C^k vector bundles, etc.

## Main definitions and constructions

* `FiberBundle.chartedSpace`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
  a charted space modelled on `B × F`.

* `FiberBundle.chartedSpace'`: Let `B` be a charted space modelled on `HB`.  Then a fiber bundle
  `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `SmoothVectorBundle`: Mixin class stating that a (topological) `VectorBundle` is smooth, in the
  sense of having smooth transition functions.

* `SmoothFiberwiseLinear.hasGroupoid`: For a smooth vector bundle `E` over `B` with fiber
  modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
  considered as charts to `B × F`, is smooth and fiberwise linear, in the sense of belonging to the
  structure groupoid `smoothFiberwiseLinear`.

* `Bundle.TotalSpace.smoothManifoldWithCorners`: A smooth vector bundle is naturally a smooth
  manifold.

* `VectorBundleCore.smoothVectorBundle`: If a (topological) `VectorBundleCore` is smooth,
  in the sense of having smooth transition functions (cf. `VectorBundleCore.IsSmooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `VectorPrebundle.smoothVectorBundle`: If a `VectorPrebundle` is smooth,
  in the sense of having smooth transition functions (cf. `VectorPrebundle.IsSmooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `Bundle.Prod.smoothVectorBundle`: The direct sum of two smooth vector bundles is a smooth vector
  bundle.
-/

set_option autoImplicit true


assert_not_exists mfderiv

open Bundle Set LocalHomeomorph

open Function (id_def)

open Filter

open scoped Manifold Bundle Topology

variable {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/


section

variable [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  {HB : Type*} [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

/-- A fiber bundle `E` over a base `B` with model fiber `F` is naturally a charted space modelled on
`B × F`. -/
instance FiberBundle.chartedSpace' : ChartedSpace (B × F) (TotalSpace F E) where
  atlas := (fun e : Trivialization F (π F E) => e.toLocalHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toLocalHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas _ := mem_image_of_mem _ (trivialization_mem_atlas F E _)
#align fiber_bundle.charted_space FiberBundle.chartedSpace'

theorem FiberBundle.chartedSpace'_chartAt (x : TotalSpace F E) :
    chartAt (B × F) x = (trivializationAt F E x.proj).toLocalHomeomorph :=
  rfl

/- Porting note: In Lean 3, the next instance was inside a section with locally reducible
`ModelProd` and it used `ModelProd B F` as the intermediate space. Using `B × F` in the middle
gives the same instance.
-/
--attribute [local reducible] ModelProd

/-- Let `B` be a charted space modelled on `HB`.  Then a fiber bundle `E` over a base `B` with model
fiber `F` is naturally a charted space modelled on `HB.prod F`. -/
instance FiberBundle.chartedSpace : ChartedSpace (ModelProd HB F) (TotalSpace F E) :=
  ChartedSpace.comp _ (B × F) _
#align fiber_bundle.charted_space' FiberBundle.chartedSpace

theorem FiberBundle.chartedSpace_chartAt (x : TotalSpace F E) :
    chartAt (ModelProd HB F) x =
      (trivializationAt F E x.proj).toLocalHomeomorph ≫ₕ
        (chartAt HB x.proj).prod (LocalHomeomorph.refl F) := by
  dsimp only [chartAt_comp, prodChartedSpace_chartAt, FiberBundle.chartedSpace'_chartAt,
    chartAt_self_eq]
  rw [Trivialization.coe_coe, Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E x.proj)]
  -- 🎉 no goals
#align fiber_bundle.charted_space_chart_at FiberBundle.chartedSpace_chartAt

theorem FiberBundle.chartedSpace_chartAt_symm_fst (x : TotalSpace F E) (y : ModelProd HB F)
    (hy : y ∈ (chartAt (ModelProd HB F) x).target) :
    ((chartAt (ModelProd HB F) x).symm y).proj = (chartAt HB x.proj).symm y.1 := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  -- ⊢ (↑(LocalHomeomorph.symm (trivializationAt F E x.proj).toLocalHomeomorph) (↑( …
  exact (trivializationAt F E x.proj).proj_symm_apply hy.2
  -- 🎉 no goals
#align fiber_bundle.charted_space_chart_at_symm_fst FiberBundle.chartedSpace_chartAt_symm_fst

end

section

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [Is : SmoothManifoldWithCorners IM M] {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

protected theorem FiberBundle.extChartAt (x : TotalSpace F E) :
    extChartAt (IB.prod 𝓘(𝕜, F)) x =
      (trivializationAt F E x.proj).toLocalEquiv ≫
        (extChartAt IB x.proj).prod (LocalEquiv.refl F) := by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, extend]
  -- ⊢ ((trivializationAt F E x.proj).toLocalHomeomorph ≫ₕ LocalHomeomorph.prod (ch …
  simp only [LocalEquiv.trans_assoc, mfld_simps]
  -- ⊢ (trivializationAt F E x.proj).toLocalHomeomorph.toLocalEquiv ≫ LocalEquiv.pr …
  -- porting note: should not be needed
  rw [LocalEquiv.prod_trans, LocalEquiv.refl_trans]
  -- 🎉 no goals
#align fiber_bundle.ext_chart_at FiberBundle.extChartAt

protected theorem FiberBundle.extChartAt_target (x : TotalSpace F E) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) x).target =
      ((extChartAt IB x.proj).target ∩
        (extChartAt IB x.proj).symm ⁻¹' (trivializationAt F E x.proj).baseSet) ×ˢ univ := by
  rw [FiberBundle.extChartAt, LocalEquiv.trans_target, Trivialization.target_eq, inter_prod]
  -- ⊢ (LocalEquiv.prod (extChartAt IB x.proj) (LocalEquiv.refl F)).target ∩ ↑(Loca …
  rfl
  -- 🎉 no goals

theorem FiberBundle.writtenInExtChartAt_trivializationAt {x : TotalSpace F E} {y}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) x
      (trivializationAt F E x.proj) y = y :=
  writtenInExtChartAt_chartAt_comp _ _ hy

theorem FiberBundle.writtenInExtChartAt_trivializationAt_symm {x : TotalSpace F E} {y}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivializationAt F E x.proj x)
      (trivializationAt F E x.proj).toLocalHomeomorph.symm y = y :=
  writtenInExtChartAt_chartAt_symm_comp _ _ hy

/-! ### Smoothness of maps in/out fiber bundles

Note: For these results we don't need that the bundle is a smooth vector bundle, or even a vector
bundle at all, just that it is a fiber bundle over a charted base space.
-/

namespace Bundle

variable {IB}

/-- Characterization of C^n functions into a smooth vector bundle. -/
theorem contMDiffWithinAt_totalSpace (f : M → TotalSpace F E) {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  simp (config := { singlePass := true }) only [contMDiffWithinAt_iff_target]
  -- ⊢ ContinuousWithinAt f s x₀ ∧ ContMDiffWithinAt IM 𝓘(𝕜, EB × F) n (↑(extChartA …
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  -- ⊢ ContinuousWithinAt f s x₀ → (ContMDiffWithinAt IM 𝓘(𝕜, EB × F) n (↑(extChart …
  intro hf
  -- ⊢ ContMDiffWithinAt IM 𝓘(𝕜, EB × F) n (↑(extChartAt (ModelWithCorners.prod IB  …
  simp_rw [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp, LocalEquiv.trans_apply,
    LocalEquiv.prod_coe, LocalEquiv.refl_coe, extChartAt_self_apply, modelWithCornersSelf_coe,
    id_def]
  refine (contMDiffWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  -- ⊢ ContMDiffWithinAt IM 𝓘(𝕜, EB) n (Prod.fst ∘ fun x => (↑(extChartAt IB (f x₀) …
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.contMDiffWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  -- ⊢ (Prod.fst ∘ fun x => (↑(extChartAt IB (f x₀).proj) (↑(trivializationAt F E ( …
  · simp_rw [Function.comp, LocalHomeomorph.coe_coe, Trivialization.coe_coe]
    -- ⊢ ↑(extChartAt IB (f x₀).proj) (↑(trivializationAt F E (f x₀).proj) (f x)).fst …
    rw [Trivialization.coe_fst']
    -- ⊢ (f x).proj ∈ (trivializationAt F E (f x₀).proj).baseSet
    exact hx
    -- 🎉 no goals
  · simp only [mfld_simps]
    -- 🎉 no goals
#align bundle.cont_mdiff_within_at_total_space Bundle.contMDiffWithinAt_totalSpace

/-- Characterization of C^n functions into a smooth vector bundle. -/
theorem contMDiffAt_totalSpace (f : M → TotalSpace F E) (x₀ : M) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_totalSpace f
  -- ⊢ ContMDiffWithinAt IM (ModelWithCorners.prod IB 𝓘(𝕜, F)) n f univ x₀ ↔ ContMD …
                                      -- 🎉 no goals
#align bundle.cont_mdiff_at_total_space Bundle.contMDiffAt_totalSpace

/-- Characterization of C^n sections of a smooth vector bundle. -/
theorem contMDiffAt_section (s : ∀ x, E x) (x₀ : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id
  -- ⊢ ContMDiffAt IB 𝓘(𝕜, F) n (fun x => (↑(trivializationAt F E x₀) (TotalSpace.m …
                                                           -- ⊢ ContMDiffAt IB IB n (fun x => x) x₀
                                                                  -- 🎉 no goals
#align bundle.cont_mdiff_at_section Bundle.contMDiffAt_section

variable (E)

theorem contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E) := fun x ↦ by
  have : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id x := contMDiffAt_id
  -- ⊢ ContMDiffAt (ModelWithCorners.prod IB 𝓘(𝕜, F)) IB n TotalSpace.proj x
  rw [contMDiffAt_totalSpace] at this
  -- ⊢ ContMDiffAt (ModelWithCorners.prod IB 𝓘(𝕜, F)) IB n TotalSpace.proj x
  exact this.1
  -- 🎉 no goals
#align bundle.cont_mdiff_proj Bundle.contMDiff_proj

theorem smooth_proj : Smooth (IB.prod 𝓘(𝕜, F)) IB (π F E) :=
  contMDiff_proj E
#align bundle.smooth_proj Bundle.smooth_proj

theorem contMDiffOn_proj {s : Set (TotalSpace F E)} :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) IB n (π F E) s :=
  (Bundle.contMDiff_proj E).contMDiffOn
#align bundle.cont_mdiff_on_proj Bundle.contMDiffOn_proj

theorem smoothOn_proj {s : Set (TotalSpace F E)} : SmoothOn (IB.prod 𝓘(𝕜, F)) IB (π F E) s :=
  contMDiffOn_proj E
#align bundle.smooth_on_proj Bundle.smoothOn_proj

theorem contMDiffAt_proj {p : TotalSpace F E} : ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p :=
  (Bundle.contMDiff_proj E).contMDiffAt
#align bundle.cont_mdiff_at_proj Bundle.contMDiffAt_proj

theorem smoothAt_proj {p : TotalSpace F E} : SmoothAt (IB.prod 𝓘(𝕜, F)) IB (π F E) p :=
  Bundle.contMDiffAt_proj E
#align bundle.smooth_at_proj Bundle.smoothAt_proj

theorem contMDiffWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    ContMDiffWithinAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) s p :=
  (Bundle.contMDiffAt_proj E).contMDiffWithinAt
#align bundle.cont_mdiff_within_at_proj Bundle.contMDiffWithinAt_proj

theorem smoothWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    SmoothWithinAt (IB.prod 𝓘(𝕜, F)) IB (π F E) s p :=
  Bundle.contMDiffWithinAt_proj E
#align bundle.smooth_within_at_proj Bundle.smoothWithinAt_proj

variable (𝕜) [∀ x, AddCommMonoid (E x)]
variable [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

theorem smooth_zeroSection : Smooth IB (IB.prod 𝓘(𝕜, F)) (zeroSection F E) := fun x ↦ by
  unfold zeroSection
  -- ⊢ ContMDiffAt IB (ModelWithCorners.prod IB 𝓘(𝕜, F)) ⊤ (fun x => { proj := x, s …
  rw [Bundle.contMDiffAt_section]
  -- ⊢ ContMDiffAt IB 𝓘(𝕜, F) ⊤ (fun x_1 => (↑(trivializationAt F E x) { proj := x_ …
  apply (contMDiffAt_const (c := 0)).congr_of_eventuallyEq
  -- ⊢ (fun x_1 => (↑(trivializationAt F E x) { proj := x_1, snd := 0 }).snd) =ᶠ[𝓝  …
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
    using congr_arg Prod.snd <| (trivializationAt F E x).zeroSection 𝕜 hy
#align bundle.smooth_zero_section Bundle.smooth_zeroSection

end Bundle

end

/-! ### Smooth vector bundles -/


variable [NontriviallyNormedField 𝕜] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B]
  [ChartedSpace HB B] [SmoothManifoldWithCorners IB B] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [Is : SmoothManifoldWithCorners IM M] {n : ℕ∞}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section WithTopology

variable [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] (F E)

variable [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- When `B` is a smooth manifold with corners with respect to a model `IB` and `E` is a
topological vector bundle over `B` with fibers isomorphic to `F`, then `SmoothVectorBundle F E IB`
registers that the bundle is smooth, in the sense of having smooth transition functions.
This is a mixin, not carrying any new data. -/
class SmoothVectorBundle : Prop where
  protected smoothOn_coordChangeL :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
        (e.baseSet ∩ e'.baseSet)
#align smooth_vector_bundle SmoothVectorBundle
#align smooth_vector_bundle.smooth_on_coord_change SmoothVectorBundle.smoothOn_coordChangeL

variable [SmoothVectorBundle F E IB]

section SmoothCoordChange

variable {F E}
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']

theorem smoothOn_coordChangeL :
    SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  SmoothVectorBundle.smoothOn_coordChangeL e e'

theorem smoothOn_symm_coordChangeL :
    SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) := by
  rw [inter_comm]
  -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(ContinuousLinearEquiv.symm (Triviali …
  refine (SmoothVectorBundle.smoothOn_coordChangeL e' e).congr fun b hb ↦ ?_
  -- ⊢ ↑(ContinuousLinearEquiv.symm (Trivialization.coordChangeL 𝕜 e e' b)) = ↑(Tri …
  rw [e.symm_coordChangeL e' hb]
  -- 🎉 no goals

theorem contMDiffOn_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  (smoothOn_coordChangeL IB e e').of_le le_top

theorem contMDiffOn_symm_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  (smoothOn_symm_coordChangeL IB e e').of_le le_top

variable {e e'}

theorem contMDiffAt_coordChangeL (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  (contMDiffOn_coordChangeL IB e e').contMDiffAt <|
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

theorem smoothAt_coordChangeL (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    SmoothAt IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  contMDiffAt_coordChangeL IB h h'

variable {IB}

protected theorem ContMDiffWithinAt.coordChangeL {f : M → B}
    (hf : ContMDiffWithinAt IM IB n f s x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s x :=
  (contMDiffAt_coordChangeL IB he he').comp_contMDiffWithinAt _ hf

protected nonrec theorem ContMDiffAt.coordChangeL {f : M → B}
    (hf : ContMDiffAt IM IB n f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  hf.coordChangeL he he'

protected theorem ContMDiffOn.coordChangeL {f : M → B}
    (hf : ContMDiffOn IM IB n f s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s :=
  fun x hx ↦ (hf x hx).coordChangeL (he hx) (he' hx)

protected theorem ContMDiff.coordChangeL {f : M → B}
    (hf : ContMDiff IM IB n f) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) := fun x ↦
  (hf x).coordChangeL (he x) (he' x)

protected nonrec theorem SmoothWithinAt.coordChangeL {f : M → B}
    (hf : SmoothWithinAt IM IB f s x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    SmoothWithinAt IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s x :=
  hf.coordChangeL he he'

protected nonrec theorem SmoothAt.coordChangeL {f : M → B}
    (hf : SmoothAt IM IB f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    SmoothAt IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  hf.coordChangeL he he'

protected nonrec theorem SmoothOn.coordChangeL {f : M → B}
    (hf : SmoothOn IM IB f s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    SmoothOn IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s :=
  hf.coordChangeL he he'

protected nonrec theorem Smooth.coordChangeL {f : M → B}
    (hf : Smooth IM IB f) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    Smooth IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) :=
  hf.coordChangeL he he'

protected theorem ContMDiffWithinAt.coordChange {f : M → B} {g : M → F}
    (hf : ContMDiffWithinAt IM IB n f s x) (hg : ContMDiffWithinAt IM 𝓘(𝕜, F) n g s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) s x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  -- ⊢ (fun y => Trivialization.coordChange e e' (f y) (g y)) =ᶠ[𝓝[s] x] fun x => ↑ …
  · have : e.baseSet ∩ e'.baseSet ∈ 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    -- ⊢ Trivialization.coordChange e e' (f y) (g y) = ↑↑(Trivialization.coordChangeL …
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
    -- 🎉 no goals
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm
    -- 🎉 no goals

protected nonrec theorem ContMDiffAt.coordChange {f : M → B} {g : M → F}
    (hf : ContMDiffAt IM IB n f x) (hg : ContMDiffAt IM 𝓘(𝕜, F) n g x) (he : f x ∈ e.baseSet)
    (he' : f x ∈ e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  hf.coordChange hg he he'

protected theorem ContMDiffOn.coordChange {f : M → B} {g : M → F} (hf : ContMDiffOn IM IB n f s)
    (hg : ContMDiffOn IM 𝓘(𝕜, F) n g s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) s := fun x hx ↦
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

protected theorem ContMDiff.coordChange {f : M → B} {g : M → F} (hf : ContMDiff IM IB n f)
    (hg : ContMDiff IM 𝓘(𝕜, F) n g) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) := fun x ↦
  (hf x).coordChange (hg x) (he x) (he' x)

protected nonrec theorem SmoothWithinAt.coordChange {f : M → B} {g : M → F}
    (hf : SmoothWithinAt IM IB f s x) (hg : SmoothWithinAt IM 𝓘(𝕜, F) g s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    SmoothWithinAt IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) s x :=
  hf.coordChange hg he he'

protected nonrec theorem SmoothAt.coordChange {f : M → B} {g : M → F} (hf : SmoothAt IM IB f x)
    (hg : SmoothAt IM 𝓘(𝕜, F) g x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    SmoothAt IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  hf.coordChange hg he he'

protected nonrec theorem SmoothOn.coordChange {f : M → B} {g : M → F} (hf : SmoothOn IM IB f s)
    (hg : SmoothOn IM 𝓘(𝕜, F) g s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    SmoothOn IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) s :=
  hf.coordChange hg he he'

protected theorem Smooth.coordChange {f : M → B} {g : M → F} (hf : Smooth IM IB f)
    (hg : Smooth IM 𝓘(𝕜, F) g) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    Smooth IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) := fun x ↦
  (hf x).coordChange (hg x) (he x) (he' x)

variable (IB e e')

theorem Trivialization.contMDiffOn_symm_trans :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (e.toLocalHomeomorph.symm ≫ₕ e'.toLocalHomeomorph) (e.target ∩ e'.target) := by
  have Hmaps : MapsTo Prod.fst (e.target ∩ e'.target) (e.baseSet ∩ e'.baseSet) := fun x hx ↦
    ⟨e.mem_target.1 hx.1, e'.mem_target.1 hx.2⟩
  rw [mapsTo_inter] at Hmaps
  -- ⊢ ContMDiffOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) (ModelWithCorners.prod IB 𝓘(𝕜 …
  -- TODO: drop `congr` #5473
  refine (contMDiffOn_fst.prod_mk
    (contMDiffOn_fst.coordChange contMDiffOn_snd Hmaps.1 Hmaps.2)).congr ?_
  rintro ⟨b, x⟩ hb
  -- ⊢ ↑(LocalHomeomorph.symm e.toLocalHomeomorph ≫ₕ e'.toLocalHomeomorph) (b, x) = …
  refine Prod.ext ?_ rfl
  -- ⊢ (↑(LocalHomeomorph.symm e.toLocalHomeomorph ≫ₕ e'.toLocalHomeomorph) (b, x)) …
  · have : (e.toLocalHomeomorph.symm (b, x)).1 ∈ e'.baseSet
    -- ⊢ (↑(LocalHomeomorph.symm e.toLocalHomeomorph) (b, x)).proj ∈ e'.baseSet
    · simp_all only [Trivialization.mem_target, mfld_simps]
      -- 🎉 no goals
    exact (e'.coe_fst' this).trans (e.proj_symm_apply hb.1)
    -- 🎉 no goals

variable {IB e e'}

theorem ContMDiffWithinAt.change_section_trivialization {f : M → TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (hf : ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x)
    (he : f x ∈ e.source) (he' : f x ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x := by
  rw [Trivialization.mem_source] at he he'
  -- ⊢ ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => (↑e' (f y)).snd) s x
  refine (hp.coordChange hf he he').congr_of_eventuallyEq ?_ ?_
  -- ⊢ (fun y => (↑e' (f y)).snd) =ᶠ[𝓝[s] x] fun y => Trivialization.coordChange e  …
  · filter_upwards [hp.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
    -- ⊢ (↑e' (f y)).snd = Trivialization.coordChange e e' ((TotalSpace.proj ∘ f) y)  …
    rw [Function.comp_apply, e.coordChange_apply_snd _ hy]
    -- 🎉 no goals
  · rw [Function.comp_apply, e.coordChange_apply_snd _ he]
    -- 🎉 no goals

theorem Trivialization.contMDiffWithinAt_snd_comp_iff₂ {f : M → TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (he : f x ∈ e.source) (he' : f x ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x ↔
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x :=
  ⟨(hp.change_section_trivialization · he he'), (hp.change_section_trivialization · he' he)⟩

end SmoothCoordChange

/-- For a smooth vector bundle `E` over `B` with fiber modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fiberwise linear. -/
instance SmoothFiberwiseLinear.hasGroupoid :
    HasGroupoid (TotalSpace F E) (smoothFiberwiseLinear B F IB) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    -- ⊢ LocalHomeomorph.symm ((fun e => e.toLocalHomeomorph) e) ≫ₕ (fun e => e.toLoc …
    haveI : MemTrivializationAtlas e := ⟨he⟩
    -- ⊢ LocalHomeomorph.symm ((fun e => e.toLocalHomeomorph) e) ≫ₕ (fun e => e.toLoc …
    haveI : MemTrivializationAtlas e' := ⟨he'⟩
    -- ⊢ LocalHomeomorph.symm ((fun e => e.toLocalHomeomorph) e) ≫ₕ (fun e => e.toLoc …
    rw [mem_smoothFiberwiseLinear_iff]
    -- ⊢ ∃ φ U hU hφ h2φ, EqOnSource (LocalHomeomorph.symm ((fun e => e.toLocalHomeom …
    refine' ⟨_, _, e.open_baseSet.inter e'.open_baseSet, smoothOn_coordChangeL IB e e',
      smoothOn_symm_coordChangeL IB e e', _⟩
    refine LocalHomeomorph.eqOnSourceSetoid.symm ⟨?_, ?_⟩
    -- ⊢ (FiberwiseLinear.localHomeomorph (fun x => Trivialization.coordChangeL 𝕜 e e …
    · simp only [e.symm_trans_source_eq e', FiberwiseLinear.localHomeomorph, trans_toLocalEquiv,
        symm_toLocalEquiv]
    · rintro ⟨b, v⟩ hb
      -- ⊢ ↑(FiberwiseLinear.localHomeomorph (fun x => Trivialization.coordChangeL 𝕜 e  …
      exact (e.apply_symm_apply_eq_coordChangeL e' hb.1 v).symm
      -- 🎉 no goals
#align smooth_fiberwise_linear.has_groupoid SmoothFiberwiseLinear.hasGroupoid

/-- A smooth vector bundle `E` is naturally a smooth manifold. -/
instance Bundle.TotalSpace.smoothManifoldWithCorners :
    SmoothManifoldWithCorners (IB.prod 𝓘(𝕜, F)) (TotalSpace F E) := by
  refine' { StructureGroupoid.HasGroupoid.comp (smoothFiberwiseLinear B F IB) _ with }
  -- ⊢ ∀ (e : LocalHomeomorph (B × F) (B × F)), e ∈ smoothFiberwiseLinear B F IB →  …
  intro e he
  -- ⊢ ChartedSpace.LiftPropOn (StructureGroupoid.IsLocalStructomorphWithinAt (cont …
  rw [mem_smoothFiberwiseLinear_iff] at he
  -- ⊢ ChartedSpace.LiftPropOn (StructureGroupoid.IsLocalStructomorphWithinAt (cont …
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  -- ⊢ ChartedSpace.LiftPropOn (StructureGroupoid.IsLocalStructomorphWithinAt (cont …
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  -- ⊢ SmoothOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) (ModelWithCorners.prod IB 𝓘(𝕜, F …
  refine' ⟨ContMDiffOn.congr _ (EqOnSource.eqOn heφ),
      ContMDiffOn.congr _ (EqOnSource.eqOn (EqOnSource.symm' heφ))⟩
  · rw [EqOnSource.source_eq heφ]
    -- ⊢ ContMDiffOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) (ModelWithCorners.prod IB 𝓘(𝕜 …
    apply smoothOn_fst.prod_mk
    -- ⊢ SmoothOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) 𝓘(𝕜, F) (fun x => ↑(φ x.fst) x.s …
    exact (hφ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd
    -- 🎉 no goals
  · rw [EqOnSource.target_eq heφ]
    -- ⊢ ContMDiffOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) (ModelWithCorners.prod IB 𝓘(𝕜 …
    apply smoothOn_fst.prod_mk
    -- ⊢ SmoothOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) 𝓘(𝕜, F) (fun x => ↑(ContinuousLi …
    exact (h2φ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd
    -- 🎉 no goals
#align bundle.total_space.smooth_manifold_with_corners Bundle.TotalSpace.smoothManifoldWithCorners

section

variable {F E}
variable {e e' : Trivialization F (π F E)} [MemTrivializationAtlas e] [MemTrivializationAtlas e']

theorem Trivialization.contMDiffWithinAt_iff {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (he : f x₀ ∈ e.source) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s x₀ :=
  (contMDiffWithinAt_totalSpace _).trans <| and_congr_right fun h ↦
    Trivialization.contMDiffWithinAt_snd_comp_iff₂ h FiberBundle.mem_trivializationAt_proj_source he

theorem Trivialization.contMDiffAt_iff {f : M → TotalSpace F E} {x₀ : M} (he : f x₀ ∈ e.source) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
      ContMDiffAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) x₀ :=
  e.contMDiffWithinAt_iff _ he

theorem Trivialization.contMDiffOn_iff {f : M → TotalSpace F E} {s : Set M}
    (he : MapsTo f s e.source) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n f s ↔
      ContMDiffOn IM IB n (fun x => (f x).proj) s ∧
      ContMDiffOn IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s := by
  simp only [ContMDiffOn, ← forall_and]
  -- ⊢ (∀ (x : M), x ∈ s → ContMDiffWithinAt IM (ModelWithCorners.prod IB 𝓘(𝕜, F))  …
  exact forall₂_congr fun x hx ↦ e.contMDiffWithinAt_iff IB (he hx)
  -- 🎉 no goals

theorem Trivialization.contMDiff_iff {f : M → TotalSpace F E} (he : ∀ x, f x ∈ e.source) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n f ↔
      ContMDiff IM IB n (fun x => (f x).proj) ∧
      ContMDiff IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) :=
  (forall_congr' fun x ↦ e.contMDiffAt_iff IB (he x)).trans forall_and

theorem Trivialization.smoothWithinAt_iff {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (he : f x₀ ∈ e.source) :
    SmoothWithinAt IM (IB.prod 𝓘(𝕜, F)) f s x₀ ↔
      SmoothWithinAt IM IB (fun x => (f x).proj) s x₀ ∧
      SmoothWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) s x₀ :=
  e.contMDiffWithinAt_iff IB he

theorem Trivialization.smoothAt_iff {f : M → TotalSpace F E} {x₀ : M} (he : f x₀ ∈ e.source) :
    SmoothAt IM (IB.prod 𝓘(𝕜, F)) f x₀ ↔
      SmoothAt IM IB (fun x => (f x).proj) x₀ ∧ SmoothAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) x₀ :=
  e.contMDiffAt_iff IB he

theorem Trivialization.smoothOn_iff {f : M → TotalSpace F E} {s : Set M}
    (he : MapsTo f s e.source) :
    SmoothOn IM (IB.prod 𝓘(𝕜, F)) f s ↔
      SmoothOn IM IB (fun x => (f x).proj) s ∧ SmoothOn IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) s :=
  e.contMDiffOn_iff IB he

theorem Trivialization.smooth_iff {f : M → TotalSpace F E} (he : ∀ x, f x ∈ e.source) :
    Smooth IM (IB.prod 𝓘(𝕜, F)) f ↔
      Smooth IM IB (fun x => (f x).proj) ∧ Smooth IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) :=
  e.contMDiff_iff IB he

theorem Trivialization.smoothOn (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    SmoothOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e e.source := by
  have : SmoothOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) id e.source := smoothOn_id
  -- ⊢ SmoothOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) (ModelWithCorners.prod IB 𝓘(𝕜, F …
  rw [e.smoothOn_iff IB (mapsTo_id _)] at this
  -- ⊢ SmoothOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) (ModelWithCorners.prod IB 𝓘(𝕜, F …
  exact (this.1.prod_mk this.2).congr fun x hx ↦ (e.mk_proj_snd hx).symm
  -- 🎉 no goals

theorem Trivialization.smoothOn_symm (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    SmoothOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e.toLocalHomeomorph.symm e.target := by
  rw [e.smoothOn_iff IB e.toLocalHomeomorph.symm_mapsTo]
  -- ⊢ SmoothOn (ModelWithCorners.prod IB 𝓘(𝕜, F)) IB (fun x => (↑(LocalHomeomorph. …
  refine ⟨smoothOn_fst.congr fun x hx ↦ e.proj_symm_apply hx, smoothOn_snd.congr fun x hx ↦ ?_⟩
  -- ⊢ (↑e (↑(LocalHomeomorph.symm e.toLocalHomeomorph) x)).snd = x.snd
  rw [e.apply_symm_apply hx]
  -- 🎉 no goals

end

/-! ### Core construction for smooth vector bundles -/

namespace VectorBundleCore

variable {ι : Type*} {F}
variable (Z : VectorBundleCore 𝕜 B F ι)

/-- Mixin for a `VectorBundleCore` stating smoothness (of transition functions). -/
class IsSmooth (IB : ModelWithCorners 𝕜 EB HB) : Prop where
  smoothOn_coordChange :
    ∀ i j, SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j)
#align vector_bundle_core.is_smooth VectorBundleCore.IsSmooth

theorem smoothOn_coordChange (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsSmooth IB] (i j : ι) :
    SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j) :=
  h.1 i j

variable [Z.IsSmooth IB]

/-- If a `VectorBundleCore` has the `IsSmooth` mixin, then the vector bundle constructed from it
is a smooth vector bundle. -/
instance smoothVectorBundle : SmoothVectorBundle F Z.Fiber IB where
  smoothOn_coordChangeL := by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(Trivialization.coordChangeL 𝕜 (Fiber …
    -- Porting note: Originally `Z.smoothOn_coordChange IB i i'`
    refine'
      (VectorBundleCore.IsSmooth.smoothOn_coordChange (Z := Z) (IB := IB) i i').congr fun b hb => _
    ext v
    -- ⊢ ↑↑(Trivialization.coordChangeL 𝕜 (FiberBundleCore.localTriv (toFiberBundleCo …
    exact Z.localTriv_coordChange_eq i i' hb v
    -- 🎉 no goals
#align vector_bundle_core.smooth_vector_bundle VectorBundleCore.smoothVectorBundle

end VectorBundleCore

/-! ### The trivial smooth vector bundle -/

/-- A trivial vector bundle over a smooth manifold is a smooth vector bundle. -/
instance Bundle.Trivial.smoothVectorBundle : SmoothVectorBundle F (Bundle.Trivial B F) IB where
  smoothOn_coordChangeL := by
    intro e e' he he'
    -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(Trivialization.coordChangeL 𝕜 e e' b …
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(Trivialization.coordChangeL 𝕜 (trivi …
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(Trivialization.coordChangeL 𝕜 (trivi …
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(ContinuousLinearEquiv.refl 𝕜 F)) ((t …
    exact smooth_const.smoothOn
    -- 🎉 no goals
#align bundle.trivial.smooth_vector_bundle Bundle.Trivial.smoothVectorBundle

/-! ### Direct sums of smooth vector bundles -/


section Prod

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]

variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] [SmoothVectorBundle F₁ E₁ IB]
  [SmoothVectorBundle F₂ E₂ IB]

/-- The direct sum of two smooth vector bundles over the same base is a smooth vector bundle. -/
instance Bundle.Prod.smoothVectorBundle : SmoothVectorBundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB where
  smoothOn_coordChangeL := by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    -- ⊢ SmoothOn IB 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₁ × F₂) (fun b => ↑(Trivialization.coordChan …
    rw [SmoothOn]
    -- ⊢ ContMDiffOn IB 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₁ × F₂) ⊤ (fun b => ↑(Trivialization.coor …
    refine' ContMDiffOn.congr _ (e₁.coordChangeL_prod 𝕜 e₁' e₂ e₂')
    -- ⊢ ContMDiffOn IB 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₁ × F₂) ⊤ (fun y => ContinuousLinearMap.p …
    refine' ContMDiffOn.clm_prodMap _ _
    -- ⊢ ContMDiffOn IB 𝓘(𝕜, F₁ →L[𝕜] F₁) ⊤ (fun y => ↑(Trivialization.coordChangeL 𝕜 …
    · refine' (smoothOn_coordChangeL IB e₁ e₁').mono _
      -- ⊢ (Trivialization.prod e₁ e₂).baseSet ∩ (Trivialization.prod e₁' e₂').baseSet  …
      simp only [Trivialization.baseSet_prod, mfld_simps]
      -- ⊢ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet) ⊆ e₁.baseSet ∩ e₁'.bas …
      mfld_set_tac
      -- 🎉 no goals
    · refine' (smoothOn_coordChangeL IB e₂ e₂').mono _
      -- ⊢ (Trivialization.prod e₁ e₂).baseSet ∩ (Trivialization.prod e₁' e₂').baseSet  …
      simp only [Trivialization.baseSet_prod, mfld_simps]
      -- ⊢ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet) ⊆ e₂.baseSet ∩ e₂'.bas …
      mfld_set_tac
      -- 🎉 no goals
#align bundle.prod.smooth_vector_bundle Bundle.Prod.smoothVectorBundle

end Prod

end WithTopology

/-! ### Prebundle construction for smooth vector bundles -/

namespace VectorPrebundle

variable [∀ x, TopologicalSpace (E x)]

/-- Mixin for a `VectorPrebundle` stating smoothness of coordinate changes. -/
class IsSmooth (a : VectorPrebundle 𝕜 F E) : Prop where
  exists_smoothCoordChange :
    ∀ᵉ (e ∈ a.pretrivializationAtlas) (e' ∈ a.pretrivializationAtlas),
      ∃ f : B → F →L[𝕜] F,
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) f (e.baseSet ∩ e'.baseSet) ∧
          ∀ (b : B) (_ : b ∈ e.baseSet ∩ e'.baseSet) (v : F),
            f b v = (e' ⟨b, e.symm b v⟩).2
#align vector_prebundle.is_smooth VectorPrebundle.IsSmooth

variable (a : VectorPrebundle 𝕜 F E) [ha : a.IsSmooth IB] {e e' : Pretrivialization F (π F E)}

/-- A randomly chosen coordinate change on a `SmoothVectorPrebundle`, given by
  the field `exists_coordChange`. Note that `a.smoothCoordChange` need not be the same as
  `a.coordChange`. -/
noncomputable def smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[𝕜] F :=
  Classical.choose (ha.exists_smoothCoordChange e he e' he') b
#align vector_prebundle.smooth_coord_change VectorPrebundle.smoothCoordChange

variable {IB}

theorem smoothOn_smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) :
    SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (a.smoothCoordChange IB he he') (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (ha.exists_smoothCoordChange e he e' he')).1
#align vector_prebundle.smooth_on_smooth_coord_change VectorPrebundle.smoothOn_smoothCoordChange

theorem smoothCoordChange_apply (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    a.smoothCoordChange IB he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (ha.exists_smoothCoordChange e he e' he')).2 b hb v
#align vector_prebundle.smooth_coord_change_apply VectorPrebundle.smoothCoordChange_apply

theorem mk_smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.smoothCoordChange IB he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  -- ⊢ (b, ↑(smoothCoordChange IB a he he' b) v).fst = (↑e' { proj := b, snd := Pre …
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    -- ⊢ (↑(LocalEquiv.symm e.toLocalEquiv) (b, v)).proj ∈ e'.baseSet
    rw [e.proj_symm_apply' hb.1]; exact hb.2
    -- ⊢ b ∈ e'.baseSet
                                  -- 🎉 no goals
  · exact a.smoothCoordChange_apply he he' hb v
    -- 🎉 no goals
#align vector_prebundle.mk_smooth_coord_change VectorPrebundle.mk_smoothCoordChange

variable (IB)
/-- Make a `SmoothVectorBundle` from a `SmoothVectorPrebundle`. -/
theorem smoothVectorBundle : @SmoothVectorBundle
    _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle a.toVectorBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; letI := a.toVectorBundle
  { smoothOn_coordChangeL := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      -- ⊢ SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b => ↑(Trivialization.coordChangeL 𝕜 (Fiber …
      refine' (a.smoothOn_smoothCoordChange he he').congr _
      -- ⊢ ∀ (y : B), y ∈ e.baseSet ∩ e'.baseSet → ↑(Trivialization.coordChangeL 𝕜 (Fib …
      intro b hb
      -- ⊢ ↑(Trivialization.coordChangeL 𝕜 (FiberPrebundle.trivializationOfMemPretrivia …
      ext v
      -- ⊢ ↑↑(Trivialization.coordChangeL 𝕜 (FiberPrebundle.trivializationOfMemPretrivi …
      rw [a.smoothCoordChange_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }
      -- 🎉 no goals
#align vector_prebundle.smooth_vector_bundle VectorPrebundle.smoothVectorBundle

end VectorPrebundle
