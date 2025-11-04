/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Differentiability of functions in vector bundles

-/

open Bundle Set OpenPartialHomeomorph ContinuousLinearMap Pretrivialization Filter

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
  · simp_rw [Function.comp, OpenPartialHomeomorph.coe_coe, Trivialization.coe_coe]
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

/-- Characterization of differentiable functions into a vector bundle in terms
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

section operations

variable {𝕜 B B' F M : Type*} {E : B → Type*}

variable
  -- Let `E` be a fiber bundle with base `B` and fiber `F` (a vector space over `𝕜`)
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [FiberBundle F E]
  -- Moreover let `E` be a vector bundle
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module 𝕜 (E x)] [VectorBundle 𝕜 F E]
  -- Let the base `B` be charted over a fixed model space `HB`
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  -- Moreover let `HB` be modelled on a normed space `EB` so that `B` (and hence `E`) have
  -- differentiable structures
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {I : ModelWithCorners 𝕜 EB HB}

variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, E x} {u : Set B} {x₀ : B}

lemma mdifferentiableWithinAt_add_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx ↦ (e.linear 𝕜 hx).1 ..
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1 ..

lemma mdifferentiableAt_add_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ht ⊢
  apply mdifferentiableWithinAt_add_section hs ht

lemma mdifferentiableOn_add_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)

lemma mdifferentiable_add_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) :=
  fun x₀ ↦ mdifferentiableAt_add_section (hs x₀) (ht x₀)

lemma mdifferentiableWithinAt_neg_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (- s x)) u x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx ↦ (e.linear 𝕜 hx).map_neg ..
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg ..

lemma mdifferentiableAt_neg_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (- s x)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact mdifferentiableWithinAt_neg_section hs

lemma mdifferentiableOn_neg_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (-s x)) u :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_neg_section (hs x₀ hx₀)

lemma mdifferentiable_neg_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (-s x)) :=
  fun x₀ ↦ mdifferentiableAt_neg_section (hs x₀)

lemma mdifferentiableWithinAt_sub_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s - t) x)) u x₀ := by
  rw [sub_eq_add_neg]
  apply mdifferentiableWithinAt_add_section hs <| mdifferentiableWithinAt_neg_section ht

lemma mdifferentiableAt_sub_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s - t) x)) x₀ := by
  rw [sub_eq_add_neg]
  apply mdifferentiableAt_add_section hs <| mdifferentiableAt_neg_section ht

lemma mDifferentiableOn_sub_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s - t) x)) u :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_sub_section (hs x₀ hx₀) (ht x₀ hx₀)

lemma mdifferentiable_sub_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s - t) x)) :=
  fun x₀ ↦ mdifferentiableAt_sub_section (hs x₀) (ht x₀)

lemma MDifferentiableWithinAt.smul_section
    (hf : MDifferentiableWithinAt I 𝓘(𝕜) f u x₀)
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) u x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx ↦ (e.linear 𝕜 hx).2 ..
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

lemma MDifferentiableAt.smul_section (hf : MDifferentiableAt I 𝓘(𝕜) f x₀)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

lemma MDifferentiableOn.smul_section (hf : MDifferentiableOn I 𝓘(𝕜) f u)
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) u :=
  fun x₀ hx₀ ↦ .smul_section (hf x₀ hx₀) (hs x₀ hx₀)

lemma mdifferentiable_smul_section (hf : MDifferentiable I 𝓘(𝕜) f)
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) :=
  fun x₀ ↦ (hf x₀).smul_section (hs x₀)

lemma mdifferentiableWithinAt_smul_const_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) u x₀ :=
  .smul_section mdifferentiableWithinAt_const hs

lemma MDifferentiableAt.smul_const_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) x₀ :=
  .smul_section mdifferentiableAt_const hs

lemma MDifferentiableOn.smul_const_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) u :=
  .smul_section mdifferentiableOn_const hs

lemma mdifferentiable_smul_const_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) :=
  fun x₀ ↦ (hs x₀).smul_const_section

lemma MDifferentiableWithinAt.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i, MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
                 (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contMDiffWithinAt_zeroSection 𝕜 E).mdifferentiableWithinAt le_rfl
  | insert i s hi h =>
    simpa [Finset.sum_insert hi] using mdifferentiableWithinAt_add_section (hs i) h

lemma MDifferentiableAt.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x} {x₀ : B}
    (hs : ∀ i, MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact MDifferentiableWithinAt.sum_section hs

lemma MDifferentiableOn.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i, MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u :=
  fun x₀ hx₀ ↦ .sum_section fun i ↦ hs i x₀ hx₀

lemma MDifferentiable.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i, MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) :=
  fun x₀ ↦ .sum_section fun i ↦ (hs i) x₀

/-- The scalar product `ψ • s` of a differentiable function `ψ : M → 𝕜` and a section `s` of a
vector bundle `V → M` is differentiable once `s` is differentiable on an open set containing
`tsupport ψ`.

See `ContMDiffOn.smul_section_of_tsupport` for the analogous result about `C^n` sections. -/
lemma MDifferentiableOn.smul_section_of_tsupport {s : Π (x : B), E x} {ψ : B → 𝕜}
    (hψ : MDifferentiableOn I 𝓘(𝕜) ψ u) (ht : IsOpen u) (ht' : tsupport ψ ⊆ u)
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (ψ x • s x)) := by
  apply mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((mdifferentiable_zeroSection _ _).mdifferentiableOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'

variable {ι : Type*} {t : ι → (x : B) → E x}

open Function

/-- The sum of a locally finite collection of sections is differentiable if each section is.
Version at a point within a set. -/
lemma MDifferentiableWithinAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) u x₀ := by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ u').Nonempty}
  have := hfin.fintype
  have : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) (u ∩ u') x₀ :=
     MDifferentiableWithinAt.sum_section fun i ↦ ((ht' i).mono inter_subset_left)
  apply (mdifferentiableWithinAt_inter hu').mp
  apply this.congr' (fun y hy ↦ ?_) inter_subset_right (mem_of_mem_nhds hu')
  rw [TotalSpace.mk_inj, tsum_eq_sum']
  refine support_subset_iff'.mpr fun i hi ↦ ?_
  by_contra! h
  have : i ∈ s.toFinset := by
    refine Set.mem_toFinset.mpr ?_
    simp only [s, ne_eq, Set.mem_setOf_eq]
    use y
    simp [h, hy]
  exact hi this

/-- The sum of a locally finite collection of sections is differentiable at `x`
if each section is. -/
lemma MDifferentiableAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

/-- The sum of a locally finite collection of sections is differentiable on a set `u`
if each section is. -/
lemma MDifferentiableOn.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) u :=
  fun x hx ↦ .sum_section_of_locallyFinite ht (ht' · x hx)

/-- The sum of a locally finite collection of sections is differentiable if each section is. -/
lemma MDifferentiable.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) :=
  fun x ↦ .sum_section_of_locallyFinite ht fun i ↦ ht' i x

lemma MDifferentiableWithinAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (∑ᶠ i, t i x)) u x₀ := by
  apply (MDifferentiableWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy ↦ ?_) (by grind) trivial
  choose U hu hfin using ht y
  have : {x | t x y ≠ 0} ⊆ {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ U).Nonempty} := by
    intro x hx
    rw [Set.mem_setOf] at hx ⊢
    use y
    simpa using ⟨hx, mem_of_mem_nhds hu⟩
  rw [tsum_eq_finsum (hfin.subset this)]

lemma MDifferentiableAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ᶠ i, t i x)) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

lemma MDifferentiableOn.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ᶠ i, t i x)) u :=
  fun x hx ↦ .finsum_section_of_locallyFinite ht fun i ↦ ht' i x hx

lemma MDifferentiable.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ᶠ i, t i x)) :=
  fun x ↦ .finsum_section_of_locallyFinite ht fun i ↦ ht' i x

end operations

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
