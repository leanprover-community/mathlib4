/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions


/-!
# Differentiability of functions in vector bundles

-/

open Bundle Set PartialHomeomorph ContinuousLinearMap Pretrivialization Filter

open scoped Manifold Bundle Topology

section


variable {𝕜 B B' F M : Type*} {E : B → Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

/-- Characterization of differentiable functions into a vector bundle. -/
theorem mdifferentiableWithinAt_totalSpace (f : M → TotalSpace F E) {s : Set M} {x₀ : M} :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x => (f x).proj) s x₀ ∧
      MDifferentiableWithinAt IM 𝓘(𝕜, F)
        (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  simp +singlePass only [mdifferentiableWithinAt_iff_target]
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  intro hf
  simp_rw [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (mdifferentiableWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.mdifferentiableWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, PartialHomeomorph.coe_coe, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

theorem mdifferentiableAt_totalSpace (f : M → TotalSpace F E) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F)) f x₀ ↔
      MDifferentiableAt IM IB (fun x => (f x).proj) x₀ ∧
      MDifferentiableAt IM 𝓘(𝕜, F)
        (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

section coordChange

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
variable {IB}

theorem mdifferentiableOn_coordChangeL :
    MDifferentiableOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  (contMDiffOn_coordChangeL e e').mdifferentiableOn le_rfl

theorem mdifferentiableOn_symm_coordChangeL :
    MDifferentiableOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) := by
  rw [inter_comm]
  refine (mdifferentiableOn_coordChangeL e' e).congr fun b hb ↦ ?_
  rw [e.symm_coordChangeL e' hb]

variable {e e'}

theorem mdifferentiableAt_coordChangeL {x : B}
    (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    MDifferentiableAt IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  (mdifferentiableOn_coordChangeL e e').mdifferentiableAt <|
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

variable {s : Set M} {f : M → B} {g : M → F} {x : M}

protected theorem MDifferentiableWithinAt.coordChangeL (hf : MDifferentiableWithinAt IM IB f s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F →L[𝕜] F)
      (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s x :=
  (mdifferentiableAt_coordChangeL he he').comp_mdifferentiableWithinAt _ hf

protected nonrec theorem MDifferentiableAt.coordChangeL
    (hf : MDifferentiableAt IM IB f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableAt IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  MDifferentiableWithinAt.coordChangeL hf he he'
  -- TODO: why no dot notation?

protected theorem MDifferentiableOn.coordChangeL
    (hf : MDifferentiableOn IM IB f s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    MDifferentiableOn IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s :=
  fun x hx ↦ (hf x hx).coordChangeL (he hx) (he' hx)

protected theorem MDifferentiable.coordChangeL
    (hf : MDifferentiable IM IB f) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    MDifferentiable IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) := fun x ↦
  (hf x).coordChangeL (he x) (he' x)

protected theorem MDifferentiableWithinAt.coordChange
    (hf : MDifferentiableWithinAt IM IB f s x) (hg : MDifferentiableWithinAt IM 𝓘(𝕜, F) g s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) s x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet ∩ e'.baseSet ∈ 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm

protected nonrec theorem MDifferentiableAt.coordChange
    (hf : MDifferentiableAt IM IB f x) (hg : MDifferentiableAt IM 𝓘(𝕜, F) g x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  MDifferentiableWithinAt.coordChange hf hg he he' -- TODO: why no dot notation?

protected theorem MDifferentiableOn.coordChange
    (hf : MDifferentiableOn IM IB f s) (hg : MDifferentiableOn IM 𝓘(𝕜, F) g s)
    (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    MDifferentiableOn IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) s := fun x hx ↦
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

protected theorem MDifferentiable.coordChange
    (hf : MDifferentiable IM IB f) (hg : MDifferentiable IM 𝓘(𝕜, F) g)
    (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    MDifferentiable IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) := fun x ↦
  (hf x).coordChange (hg x) (he x) (he' x)

end coordChange

end

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` can not be always be stated as differentiability of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sense when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableWithinAt`. We also give a version for `MDifferentiableAt`, but no
version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written in coordinates,
only makes sense around a point.
-/
lemma MDifferentiableWithinAt.clm_apply_of_inCoordinates
    (hϕ : MDifferentiableWithinAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : MDifferentiableWithinAt IM (IB₁.prod 𝓘(𝕜, F₁)) (fun m ↦ (v m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : MDifferentiableWithinAt IM IB₂ b₂ s m₀) :
    MDifferentiableWithinAt IM (IB₂.prod 𝓘(𝕜, F₂))
      (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) s m₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_insert
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.insert.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.insert.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp only [coe_comp', ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply, Function.comp_apply]
  congr
  rw [Trivialization.symm_apply_apply_mk (trivializationAt F₁ E₁ (b₁ m₀)) hm (v m)]

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` can not be always be stated as differentiability of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sense when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableAt`. We also give a version for `MDifferentiableWithinAt`,
but no version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written
in coordinates, only makes sense around a point.
-/
lemma MDifferentiableAt.clm_apply_of_inCoordinates
    (hϕ : MDifferentiableAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : MDifferentiableAt IM (IB₁.prod 𝓘(𝕜, F₁)) (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : MDifferentiableAt IM IB₂ b₂ m₀) :
    MDifferentiableAt IM (IB₂.prod 𝓘(𝕜, F₂)) (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end
