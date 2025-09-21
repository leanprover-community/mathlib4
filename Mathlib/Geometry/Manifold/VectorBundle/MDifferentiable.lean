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


/-- Characterization of differentiable functions into a vector bundle.
Version at a point within a set -/
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

/-- Characterization of differentiable functions into a vector bundle.
Version at a point -/
theorem mdifferentiableAt_totalSpace (f : M → TotalSpace F E) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F)) f x₀ ↔
      MDifferentiableAt IM IB (fun x => (f x).proj) x₀ ∧
      MDifferentiableAt IM 𝓘(𝕜, F)
        (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

/-- Characterization of differentiable sections of a vector bundle at a point within a set
in terms of the preferred trivialization at that point. -/
theorem mdifferentiableWithinAt_section (s : Π b, E b) {u : Set B} {b₀ : B} :
    MDifferentiableWithinAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) u b₀ ↔
      MDifferentiableWithinAt IB 𝓘(𝕜, F) (fun b ↦ (trivializationAt F E b₀ (s b)).2) u b₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  change MDifferentiableWithinAt _ _ id _ _ ∧ _ ↔ _
  simp [mdifferentiableWithinAt_id]

/-- Characterization of differentiable sections of a vector bundle at a point within a set
in terms of the preferred trivialization at that point. -/
theorem mdifferentiableAt_section (s : Π b, E b) {b₀ : B} :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) b₀ ↔
      MDifferentiableAt IB 𝓘(𝕜, F) (fun b ↦ (trivializationAt F E b₀ (s b)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_section _ _

namespace Bundle

variable (E) {IB}

theorem mdifferentiable_proj : MDifferentiable (IB.prod 𝓘(𝕜, F)) IB (π F E) := fun x ↦ by
  have : MDifferentiableAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) id x := mdifferentiableAt_id
  rw [mdifferentiableAt_totalSpace] at this
  exact this.1

theorem mdifferentiableOn_proj {s : Set (TotalSpace F E)} :
    MDifferentiableOn (IB.prod 𝓘(𝕜, F)) IB (π F E) s :=
  (mdifferentiable_proj E).mdifferentiableOn

theorem mdifferentiableAt_proj {p : TotalSpace F E} :
    MDifferentiableAt (IB.prod 𝓘(𝕜, F)) IB (π F E) p :=
  (mdifferentiable_proj E).mdifferentiableAt

theorem mdifferentiableWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    MDifferentiableWithinAt (IB.prod 𝓘(𝕜, F)) IB (π F E) s p :=
  (mdifferentiableAt_proj E).mdifferentiableWithinAt

variable (𝕜) [∀ x, AddCommMonoid (E x)]
variable [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

theorem mdifferentiable_zeroSection : MDifferentiable IB (IB.prod 𝓘(𝕜, F)) (zeroSection F E) := by
  intro x
  unfold zeroSection
  rw [mdifferentiableAt_section]
  apply (mdifferentiableAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
    using congr_arg Prod.snd <| (trivializationAt F E x).zeroSection 𝕜 hy

theorem mdifferentiableOn_zeroSection {t : Set B} :
    MDifferentiableOn IB (IB.prod 𝓘(𝕜, F)) (zeroSection F E) t :=
  (mdifferentiable_zeroSection _ _).mdifferentiableOn

theorem mdifferentiableAt_zeroSection {x : B} :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (zeroSection F E) x :=
  (mdifferentiable_zeroSection _ _).mdifferentiableAt

theorem mdifferentiableWithinAt_zeroSection {t : Set B} {x : B} :
    MDifferentiableWithinAt IB (IB.prod 𝓘(𝕜, F)) (zeroSection F E) t x :=
  (mdifferentiable_zeroSection _ _ x).mdifferentiableWithinAt

end Bundle

section coordChange

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
variable {IB}

theorem mdifferentiableOn_coordChangeL :
    MDifferentiableOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  (contMDiffOn_coordChangeL e e').mdifferentiableOn le_rfl

theorem mdifferentiableOn_symm_coordChangeL :
    MDifferentiableOn IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B ↦ ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  (contMDiffOn_symm_coordChangeL e e').mdifferentiableOn le_rfl

variable {e e'}

theorem mdifferentiableAt_coordChangeL {x : B}
    (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    MDifferentiableAt IB 𝓘(𝕜, F →L[𝕜] F) (fun b : B ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  (contMDiffAt_coordChangeL h h').mdifferentiableAt le_rfl

variable {s : Set M} {f : M → B} {g : M → F} {x : M}

protected theorem MDifferentiableWithinAt.coordChangeL (hf : MDifferentiableWithinAt IM IB f s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F →L[𝕜] F)
      (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s x :=
  (mdifferentiableAt_coordChangeL he he').comp_mdifferentiableWithinAt _ hf

protected theorem MDifferentiableAt.coordChangeL
    (hf : MDifferentiableAt IM IB f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableAt IM 𝓘(𝕜, F →L[𝕜] F) (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  MDifferentiableWithinAt.coordChangeL hf he he'

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

protected theorem MDifferentiableAt.coordChange
    (hf : MDifferentiableAt IM IB f x) (hg : MDifferentiableAt IM 𝓘(𝕜, F) g x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  MDifferentiableWithinAt.coordChange hf hg he he'

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

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]

lemma MDifferentiableWithinAt.change_section_trivialization
    {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
    {e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (hf : MDifferentiableWithinAt IM IB (π F E ∘ f) s x₀)
    (he'f : MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) s x₀)
    (he : f x₀ ∈ e.source) (he' : f x₀ ∈ e'.source) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e' (f x)).2) s x₀ := by
  rw [Trivialization.mem_source] at he he'
  refine (hf.coordChange he'f he he').congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hf.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
    rw [Function.comp_apply, e.coordChange_apply_snd e' hy]
  · rw [Function.comp_apply, e.coordChange_apply_snd _ he]

theorem Trivialization.mdifferentiableWithinAt_snd_comp_iff₂
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (hex₀ : f x₀ ∈ e.source) (he'x₀ : f x₀ ∈ e'.source)
    (hf : MDifferentiableWithinAt IM IB (π F E ∘ f) s x₀) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) s x₀ ↔
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e' (f x)).2) s x₀ :=
  ⟨(hf.change_section_trivialization IB · hex₀ he'x₀),
   (hf.change_section_trivialization IB · he'x₀ hex₀)⟩

variable (e e')

theorem Trivialization.mdifferentiableAt_snd_comp_iff₂
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {x₀ : M}
    (he : f x₀ ∈ e.source) (he' : f x₀ ∈ e'.source)
    (hf : MDifferentiableAt IM IB (fun x ↦ (f x).proj) x₀) :
    MDifferentiableAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) x₀ ↔
    MDifferentiableAt IM 𝓘(𝕜, F) (fun x ↦ (e' (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using
    e.mdifferentiableWithinAt_snd_comp_iff₂ IB he he' hf

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point within at set. -/
theorem Trivialization.mdifferentiableWithinAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (f : M → TotalSpace F E) {s : Set M} {x₀ : M}
    (he : f x₀ ∈ e.source) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x => (f x).proj) s x₀ ∧
      MDifferentiableWithinAt IM 𝓘(𝕜, F)
        (fun x ↦ (e (f x)).2) s x₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableWithinAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point. -/
theorem Trivialization.mdifferentiableAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (f : M → TotalSpace F E) {x₀ : M}
    (he : f x₀ ∈ e.source) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F)) f x₀ ↔
      MDifferentiableAt IM IB (fun x => (f x).proj) x₀ ∧
      MDifferentiableAt IM 𝓘(𝕜, F)
        (fun x ↦ (e (f x)).2) x₀ := by
  rw [mdifferentiableAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

/-- Characterization of differentiable sections a vector bundle in terms
of any trivialization. Version at a point within at set. -/
theorem Trivialization.mdifferentiableWithinAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {u : Set B} {b₀ : B}
    (hex₀ : b₀ ∈ e.baseSet) :
    MDifferentiableWithinAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) u b₀ ↔
      MDifferentiableWithinAt IB 𝓘(𝕜, F) (fun x ↦ (e (s x)).2) u b₀ := by
  rw [e.mdifferentiableWithinAt_totalSpace_iff IB]
  · change MDifferentiableWithinAt IB IB id u b₀ ∧ _ ↔ _
    simp [mdifferentiableWithinAt_id]
  exact (coe_mem_source e).mpr hex₀

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point. -/
theorem Trivialization.mdifferentiableAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {b₀ : B}
    (hex₀ : b₀ ∈ e.baseSet) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) b₀ ↔
      MDifferentiableAt IB 𝓘(𝕜, F) (fun x ↦ (e (s x)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using e.mdifferentiableWithinAt_section_iff IB s hex₀

variable {IB} in
/-- Differentiability of a section on `s` can be determined
using any trivialisation whose `baseSet` contains `s`. -/
theorem Trivialization.mdifferentiableOn_section_iff {s : ∀ x, E x} {a : Set B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (ha : IsOpen a) (ha' : a ⊆ e.baseSet) :
    MDifferentiableOn IB (IB.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) a ↔
      MDifferentiableOn IB 𝓘(𝕜, F) (fun x ↦ (e ⟨x, s x⟩).2) a := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩ <;>
  have := (h x hx).mdifferentiableAt <| ha.mem_nhds hx
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mp this).mdifferentiableWithinAt
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mpr this).mdifferentiableWithinAt

variable {IB} in
/-- For any trivialization `e`, the differentiability of a section on `e.baseSet`
can be determined using `e`. -/
theorem Trivialization.mdifferentiableOn_section_baseSet_iff {s : ∀ x, E x}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] :
    MDifferentiableOn IB (IB.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) e.baseSet ↔
      MDifferentiableOn IB 𝓘(𝕜, F) (fun x ↦ (e ⟨x, s x⟩).2) e.baseSet :=
  e.mdifferentiableOn_section_iff e.open_baseSet subset_rfl

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

Note that the differentiability of `ϕ` cannot be always be stated as differentiability of a map
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

Note that the differentiability of `ϕ` cannot be always be stated as differentiability of a map
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
