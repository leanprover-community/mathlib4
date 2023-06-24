/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth

! This file was ported from Lean 3 source module geometry.manifold.vector_bundle.basic
! leanprover-community/mathlib commit f9ec187127cc5b381dfcf5f4a22dacca4c20b63d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.VectorBundle.FiberwiseLinear
import Mathbin.Topology.VectorBundle.Constructions

/-! # Smooth vector bundles

This file defines smooth vector bundles over a smooth manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`.  We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`

Now, we define `smooth_vector_bundle` as the `Prop` of having smooth transition functions.
Recall the structure groupoid `smooth_fiberwise_linear` on `B × F` consisting of smooth, fiberwise
linear local homeomorphisms.  We show that our definition of "smooth vector bundle" implies
`has_groupoid` for this groupoid, and show (by a "composition" of `has_groupoid` instances) that
this means that a smooth vector bundle is a smooth manifold.

Since `smooth_vector_bundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be smooth vector bundles over several different base
fields, they can also be C^k vector bundles, etc.

## Main definitions and constructions

* `fiber_bundle.charted_space`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
  a charted space modelled on `B × F`.

* `fiber_bundle.charted_space'`: Let `B` be a charted space modelled on `HB`.  Then a fiber bundle
  `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `smooth_vector_bundle`: Mixin class stating that a (topological) `vector_bundle` is smooth, in the
  sense of having smooth transition functions.

* `smooth_fiberwise_linear.has_groupoid`: For a smooth vector bundle `E` over `B` with fiber
  modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
  considered as charts to `B × F`, is smooth and fiberwise linear, in the sense of belonging to the
  structure groupoid `smooth_fiberwise_linear`.

* `bundle.total_space.smooth_manifold_with_corners`: A smooth vector bundle is naturally a smooth
  manifold.

* `vector_bundle_core.smooth_vector_bundle`: If a (topological) `vector_bundle_core` is smooth,
  in the sense of having smooth transition functions (cf. `vector_bundle_core.is_smooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `vector_prebundle.smooth_vector_bundle`: If a `vector_prebundle` is smooth,
  in the sense of having smooth transition functions (cf. `vector_prebundle.is_smooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `bundle.prod.smooth_vector_bundle`: The direct sum of two smooth vector bundles is a smooth vector
  bundle.
-/


assert_not_exists mfderiv

open Bundle Set LocalHomeomorph

open Function (id_def)

open Filter

open scoped Manifold Bundle Topology

variable {𝕜 B B' F M : Type _} {E : B → Type _}

/-! ### Charted space structure on a fiber bundle -/


section

variable [TopologicalSpace F] [TopologicalSpace (TotalSpace E)] [∀ x, TopologicalSpace (E x)]
  {HB : Type _} [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

/-- A fiber bundle `E` over a base `B` with model fiber `F` is naturally a charted space modelled on
`B × F`. -/
instance FiberBundle.chartedSpace : ChartedSpace (B × F) (TotalSpace E)
    where
  atlas := (fun e : Trivialization F (π E) => e.toLocalHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toLocalHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas x := mem_image_of_mem _ (trivialization_mem_atlas F E _)
#align fiber_bundle.charted_space FiberBundle.chartedSpace

section

attribute [local reducible] ModelProd

/-- Let `B` be a charted space modelled on `HB`.  Then a fiber bundle `E` over a base `B` with model
fiber `F` is naturally a charted space modelled on `HB.prod F`. -/
instance FiberBundle.chartedSpace' : ChartedSpace (ModelProd HB F) (TotalSpace E) :=
  ChartedSpace.comp _ (ModelProd B F) _
#align fiber_bundle.charted_space' FiberBundle.chartedSpace'

end

theorem FiberBundle.chartedSpace_chartAt (x : TotalSpace E) :
    chartAt (ModelProd HB F) x =
      (trivializationAt F E x.proj).toLocalHomeomorph ≫ₕ
        (chartAt HB x.proj).Prod (LocalHomeomorph.refl F) :=
  by
  dsimp only [FiberBundle.chartedSpace', ChartedSpace.comp, FiberBundle.chartedSpace,
    prodChartedSpace, chartedSpaceSelf]
  rw [Trivialization.coe_coe, Trivialization.coe_fst' _ (mem_base_set_trivialization_at F E x.proj)]
#align fiber_bundle.charted_space_chart_at FiberBundle.chartedSpace_chartAt

theorem FiberBundle.chartedSpace_chartAt_symm_fst (x : TotalSpace E) (y : ModelProd HB F)
    (hy : y ∈ (chartAt (ModelProd HB F) x).target) :
    ((chartAt (ModelProd HB F) x).symm y).proj = (chartAt HB x.proj).symm y.1 :=
  by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  exact (trivialization_at F E x.proj).proj_symm_apply hy.2
#align fiber_bundle.charted_space_chart_at_symm_fst FiberBundle.chartedSpace_chartAt_symm_fst

end

section

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace E)] [∀ x, TopologicalSpace (E x)] {EB : Type _}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type _} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (E' : B → Type _) [∀ x, Zero (E' x)] {EM : Type _}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type _} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [Is : SmoothManifoldWithCorners IM M] {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

protected theorem FiberBundle.extChartAt (x : TotalSpace E) :
    extChartAt (IB.Prod 𝓘(𝕜, F)) x =
      (trivializationAt F E x.proj).toLocalEquiv ≫
        (extChartAt IB x.proj).Prod (LocalEquiv.refl F) :=
  by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, extend]
  simp only [LocalEquiv.trans_assoc, mfld_simps]
#align fiber_bundle.ext_chart_at FiberBundle.extChartAt

/-! ### Smoothness of maps in/out fiber bundles

Note: For these results we don't need that the bundle is a smooth vector bundle, or even a vector
bundle at all, just that it is a fiber bundle over a charted base space.
-/


namespace Bundle

variable {F E IB}

/-- Characterization of C^n functions into a smooth vector bundle. -/
theorem contMDiffWithinAt_totalSpace (f : M → TotalSpace E) {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.Prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
        ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) s x₀ :=
  by
  simp (config := { singlePass := true }) only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm, ← continuous_within_at_total_space, and_congr_right_iff]
  intro hf
  simp_rw [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp, LocalEquiv.trans_apply,
    LocalEquiv.prod_coe, LocalEquiv.refl_coe, extChartAt_self_apply, modelWithCornersSelf_coe,
    id_def]
  refine' (contMDiffWithinAt_prod_iff _).trans _
  -- rw doesn't do this?
  have h1 : (fun x => (f x).proj) ⁻¹' (trivialization_at F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((continuous_proj F E).ContinuousWithinAt.comp hf (maps_to_image f s)).preimage_mem_nhdsWithin
      ((Trivialization.open_baseSet _).mem_nhds (mem_base_set_trivialization_at F E _))
  refine'
    and_congr (eventually_eq.cont_mdiff_within_at_iff (eventually_of_mem h1 fun x hx => _) _)
      Iff.rfl
  · simp_rw [Function.comp, LocalHomeomorph.coe_coe, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]
#align bundle.cont_mdiff_within_at_total_space Bundle.contMDiffWithinAt_totalSpace

/-- Characterization of C^n functions into a smooth vector bundle. -/
theorem contMDiffAt_totalSpace (f : M → TotalSpace E) (x₀ : M) :
    ContMDiffAt IM (IB.Prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀ :=
  by simp_rw [← contMDiffWithinAt_univ]; exact cont_mdiff_within_at_total_space f
#align bundle.cont_mdiff_at_total_space Bundle.contMDiffAt_totalSpace

/-- Characterization of C^n sections of a smooth vector bundle. -/
theorem contMDiffAt_section (s : ∀ x, E x) (x₀ : B) :
    ContMDiffAt IB (IB.Prod 𝓘(𝕜, F)) n (fun x => totalSpaceMk x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x => (trivializationAt F E x₀ (totalSpaceMk x (s x))).2) x₀ :=
  by simp_rw [cont_mdiff_at_total_space, and_iff_right_iff_imp]; intro x; exact contMDiffAt_id
#align bundle.cont_mdiff_at_section Bundle.contMDiffAt_section

variable (E)

theorem contMDiff_proj : ContMDiff (IB.Prod 𝓘(𝕜, F)) IB n (π E) :=
  by
  intro x
  rw [ContMDiffAt, contMDiffWithinAt_iff']
  refine' ⟨(continuous_proj F E).ContinuousWithinAt, _⟩
  simp_rw [(· ∘ ·), FiberBundle.extChartAt]
  apply cont_diff_within_at_fst.congr
  · rintro ⟨a, b⟩ hab
    simp only [mfld_simps] at hab 
    have : ((chart_at HB x.1).symm (IB.symm a), b) ∈ (trivialization_at F E x.fst).target := by
      simp only [hab, mfld_simps]
    simp only [Trivialization.proj_symm_apply _ this, hab, mfld_simps]
  · simp only [mfld_simps]
#align bundle.cont_mdiff_proj Bundle.contMDiff_proj

theorem smooth_proj : Smooth (IB.Prod 𝓘(𝕜, F)) IB (π E) :=
  contMDiff_proj E
#align bundle.smooth_proj Bundle.smooth_proj

theorem contMDiffOn_proj {s : Set (TotalSpace E)} : ContMDiffOn (IB.Prod 𝓘(𝕜, F)) IB n (π E) s :=
  (Bundle.contMDiff_proj E).ContMDiffOn
#align bundle.cont_mdiff_on_proj Bundle.contMDiffOn_proj

theorem smoothOn_proj {s : Set (TotalSpace E)} : SmoothOn (IB.Prod 𝓘(𝕜, F)) IB (π E) s :=
  contMDiffOn_proj E
#align bundle.smooth_on_proj Bundle.smoothOn_proj

theorem contMDiffAt_proj {p : TotalSpace E} : ContMDiffAt (IB.Prod 𝓘(𝕜, F)) IB n (π E) p :=
  (Bundle.contMDiff_proj E).ContMDiffAt
#align bundle.cont_mdiff_at_proj Bundle.contMDiffAt_proj

theorem smoothAt_proj {p : TotalSpace E} : SmoothAt (IB.Prod 𝓘(𝕜, F)) IB (π E) p :=
  Bundle.contMDiffAt_proj E
#align bundle.smooth_at_proj Bundle.smoothAt_proj

theorem contMDiffWithinAt_proj {s : Set (TotalSpace E)} {p : TotalSpace E} :
    ContMDiffWithinAt (IB.Prod 𝓘(𝕜, F)) IB n (π E) s p :=
  (Bundle.contMDiffAt_proj E).ContMDiffWithinAt
#align bundle.cont_mdiff_within_at_proj Bundle.contMDiffWithinAt_proj

theorem smoothWithinAt_proj {s : Set (TotalSpace E)} {p : TotalSpace E} :
    SmoothWithinAt (IB.Prod 𝓘(𝕜, F)) IB (π E) s p :=
  Bundle.contMDiffWithinAt_proj E
#align bundle.smooth_within_at_proj Bundle.smoothWithinAt_proj

variable (𝕜 E) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

theorem smooth_zeroSection : Smooth IB (IB.Prod 𝓘(𝕜, F)) (zeroSection E) :=
  by
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  refine' ⟨contMDiffAt_id, cont_mdiff_at_const.congr_of_eventually_eq _⟩
  · exact 0
  refine'
    eventually_of_mem
      ((trivialization_at F E x).open_baseSet.mem_nhds (mem_base_set_trivialization_at F E x))
      fun x' hx' => _
  simp_rw [zero_section_proj, (trivialization_at F E x).zeroSection 𝕜 hx']
#align bundle.smooth_zero_section Bundle.smooth_zeroSection

end Bundle

end

/-! ### Smooth vector bundles -/


variable [NontriviallyNormedField 𝕜] {EB : Type _} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type _} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B]
  [ChartedSpace HB B] [SmoothManifoldWithCorners IB B] {EM : Type _} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type _} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [Is : SmoothManifoldWithCorners IM M] {n : ℕ∞}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section WithTopology

variable [TopologicalSpace (TotalSpace E)] [∀ x, TopologicalSpace (E x)]

variable (F E) [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- When `B` is a smooth manifold with corners with respect to a model `IB` and `E` is a
topological vector bundle over `B` with fibers isomorphic to `F`, then `smooth_vector_bundle F E IB`
registers that the bundle is smooth, in the sense of having smooth transition functions.
This is a mixin, not carrying any new data`. -/
class SmoothVectorBundle : Prop where
  smoothOn_coord_change :
    ∀ (e e' : Trivialization F (π E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
        (e.baseSet ∩ e'.baseSet)
#align smooth_vector_bundle SmoothVectorBundle

export SmoothVectorBundle (smoothOn_coord_change)

variable [SmoothVectorBundle F E IB]

/-- For a smooth vector bundle `E` over `B` with fiber modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fiberwise linear. -/
instance : HasGroupoid (TotalSpace E) (smoothFiberwiseLinear B F IB)
    where compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    haveI : MemTrivializationAtlas e := ⟨he⟩
    haveI : MemTrivializationAtlas e' := ⟨he'⟩
    skip
    rw [mem_smoothFiberwiseLinear_iff]
    refine' ⟨_, _, e.open_base_set.inter e'.open_base_set, smooth_on_coord_change e e', _, _, _⟩
    · rw [inter_comm]
      apply ContMDiffOn.congr (smooth_on_coord_change e' e)
      · intro b hb
        rw [e.symm_coord_changeL e' hb]
      · infer_instance
      · infer_instance
    ·
      simp only [e.symm_trans_source_eq e', FiberwiseLinear.localHomeomorph, trans_to_local_equiv,
        symm_to_local_equiv]
    · rintro ⟨b, v⟩ hb
      have hb' : b ∈ e.base_set ∩ e'.base_set := by
        simpa only [trans_to_local_equiv, symm_to_local_equiv, e.symm_trans_source_eq e',
          coe_coe_symm, prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hb
      exact e.apply_symm_apply_eq_coord_changeL e' hb' v

/-- A smooth vector bundle `E` is naturally a smooth manifold. -/
instance : SmoothManifoldWithCorners (IB.Prod 𝓘(𝕜, F)) (TotalSpace E) :=
  by
  refine' { StructureGroupoid.HasGroupoid.comp (smoothFiberwiseLinear B F IB) _ with }
  intro e he
  rw [mem_smoothFiberwiseLinear_iff] at he 
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine' ⟨ContMDiffOn.congr _ heφ.eq_on, ContMDiffOn.congr _ heφ.symm'.eq_on⟩
  · rw [heφ.source_eq]
    apply smooth_on_fst.prod_mk
    exact (hφ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd
  · rw [heφ.target_eq]
    apply smooth_on_fst.prod_mk
    exact (h2φ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd

/-! ### Core construction for smooth vector bundles -/


namespace VectorBundleCore

variable {ι : Type _} {F} (Z : VectorBundleCore 𝕜 B F ι)

/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`smoothOn_coord_change] [] -/
/-- Mixin for a `vector_bundle_core` stating smoothness (of transition functions). -/
class IsSmooth (IB : ModelWithCorners 𝕜 EB HB) : Prop where
  smoothOn_coord_change :
    ∀ i j, SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j)
#align vector_bundle_core.is_smooth VectorBundleCore.IsSmooth

/- ./././Mathport/Syntax/Translate/Command.lean:240:13: unsupported: advanced export style -/
export IsSmooth ()

variable [Z.IsSmooth IB]

/-- If a `vector_bundle_core` has the `is_smooth` mixin, then the vector bundle constructed from it
is a smooth vector bundle. -/
instance smoothVectorBundle : SmoothVectorBundle F Z.Fiber IB
    where smoothOn_coord_change := by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    refine' (Z.smooth_on_coord_change IB i i').congr fun b hb => _
    ext v
    exact Z.local_triv_coord_change_eq i i' hb v
#align vector_bundle_core.smooth_vector_bundle VectorBundleCore.smoothVectorBundle

end VectorBundleCore

/-! ### The trivial smooth vector bundle -/


/-- A trivial vector bundle over a smooth manifold is a smooth vector bundle. -/
instance Bundle.Trivial.smoothVectorBundle : SmoothVectorBundle F (Bundle.Trivial B F) IB
    where smoothOn_coord_change := by
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact smooth_const.smooth_on
#align bundle.trivial.smooth_vector_bundle Bundle.Trivial.smoothVectorBundle

/-! ### Direct sums of smooth vector bundles -/


section Prod

variable (F₁ : Type _) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type _)
  [TopologicalSpace (TotalSpace E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]

variable (F₂ : Type _) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type _)
  [TopologicalSpace (TotalSpace E₂)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] [SmoothVectorBundle F₁ E₁ IB]
  [SmoothVectorBundle F₂ E₂ IB]

/-- The direct sum of two smooth vector bundles over the same base is a smooth vector bundle. -/
instance Bundle.Prod.smoothVectorBundle : SmoothVectorBundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB
    where smoothOn_coord_change :=
    by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    skip
    rw [SmoothOn]
    refine' ContMDiffOn.congr _ (e₁.coord_changeL_prod 𝕜 e₁' e₂ e₂')
    refine' ContMDiffOn.clm_prodMap _ _
    · refine' (smooth_on_coord_change e₁ e₁').mono _
      simp only [Trivialization.baseSet_prod, mfld_simps]
      mfld_set_tac
    · refine' (smooth_on_coord_change e₂ e₂').mono _
      simp only [Trivialization.baseSet_prod, mfld_simps]
      mfld_set_tac
#align bundle.prod.smooth_vector_bundle Bundle.Prod.smoothVectorBundle

end Prod

end WithTopology

/-! ### Prebundle construction for smooth vector bundles -/


namespace VectorPrebundle

variable [∀ x, TopologicalSpace (E x)] {F E}

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (e e' «expr ∈ » a.pretrivialization_atlas) -/
/-- Mixin for a `vector_prebundle` stating smoothness of coordinate changes. -/
class IsSmooth (a : VectorPrebundle 𝕜 F E) : Prop where
  exists_smooth_coord_change :
    ∀ (e) (_ : e ∈ a.pretrivializationAtlas) (e') (_ : e' ∈ a.pretrivializationAtlas),
      ∃ f : B → F →L[𝕜] F,
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) f (e.baseSet ∩ e'.baseSet) ∧
          ∀ (b : B) (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F),
            f b v = (e' (totalSpaceMk b (e.symm b v))).2
#align vector_prebundle.is_smooth VectorPrebundle.IsSmooth

variable (a : VectorPrebundle 𝕜 F E) [ha : a.IsSmooth IB] {e e' : Pretrivialization F (π E)}

/-- A randomly chosen coordinate change on a `smooth_vector_prebundle`, given by
  the field `exists_coord_change`. Note that `a.smooth_coord_change` need not be the same as
  `a.coord_change`. -/
noncomputable def smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[𝕜] F :=
  Classical.choose (ha.exists_smooth_coord_change e he e' he') b
#align vector_prebundle.smooth_coord_change VectorPrebundle.smoothCoordChange

variable {IB}

theorem smoothOn_smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) :
    SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (a.smoothCoordChange IB he he') (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (ha.exists_smooth_coord_change e he e' he')).1
#align vector_prebundle.smooth_on_smooth_coord_change VectorPrebundle.smoothOn_smoothCoordChange

theorem smoothCoordChange_apply (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    a.smoothCoordChange IB he he' b v = (e' (totalSpaceMk b (e.symm b v))).2 :=
  (Classical.choose_spec (ha.exists_smooth_coord_change e he e' he')).2 b hb v
#align vector_prebundle.smooth_coord_change_apply VectorPrebundle.smoothCoordChange_apply

theorem mk_smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.smoothCoordChange IB he he' b v) = e' (totalSpaceMk b (e.symm b v)) :=
  by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.smooth_coord_change_apply he he' hb v
#align vector_prebundle.mk_smooth_coord_change VectorPrebundle.mk_smoothCoordChange

variable (IB)

/-- Make a `smooth_vector_bundle` from a `smooth_vector_prebundle`.  -/
theorem smoothVectorBundle :
    @SmoothVectorBundle _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle
      a.to_vectorBundle :=
  {
    smoothOn_coord_change := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine' (a.smooth_on_smooth_coord_change he he').congr _
      intro b hb
      ext v
      rw [a.smooth_coord_change_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }
#align vector_prebundle.smooth_vector_bundle VectorPrebundle.smoothVectorBundle

end VectorPrebundle

