/-
Copyright (c) 2023 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! # Pullbacks of `C^n` vector bundles

This file defines pullbacks of `C^n` vector bundles over a manifold.

## Main definitions

* `ContMDiffVectorBundle.pullback`: For a `C^n` vector bundle `E` over a manifold `B` and a `C^n`
  map `f : B' → B`, the pullback vector bundle `f *ᵖ E` is a `C^n` vector bundle.

-/

open Bundle Set
open scoped Manifold Topology

variable {𝕜 B B' : Type*} (F : Type*) (E : B → Type*) {n : WithTop ℕ∞}
variable [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EB' : Type*} [NormedAddCommGroup EB']
  [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners 𝕜 EB' HB'}
  [TopologicalSpace B'] [ChartedSpace HB' B'] [FiberBundle F E]
  {M EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  (f : ContMDiffMap IB' IB B' B n)

/-- For a fiber bundle `E` over a manifold `B` and a regular map `f : B' → B`, the natural
"lift" map from the total space of `f *ᵖ E` to the total space of `E` is regular. -/
theorem Bundle.Pullback.contMDiff_lift :
    ContMDiff (IB'.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (Pullback.lift f : TotalSpace F (f *ᵖ E) → TotalSpace F E) := by
  intro x
  rw [contMDiffAt_totalSpace]
  refine ⟨f.contMDiff.contMDiffAt.comp _ (contMDiffAt_proj (f *ᵖ E)), ?_⟩
  simp only [contMDiffAt_of_totalSpace, trivializationAt, lift_proj, FiberBundle.trivializationAt']
  apply ContMDiffAt.congr_of_eventuallyEq contMDiffAt_snd
  have : (trivializationAt F (f *ᵖ E) x.proj).target ∈
      𝓝 ((trivializationAt F (f *ᵖ E) x.proj) x) := by
    apply IsOpen.mem_nhds
    · exact (trivializationAt F (f *ᵖ E) x.proj).open_target
    · simpa [Trivialization.mem_target] using FiberBundle.mem_baseSet_trivializationAt' x.proj
  filter_upwards [this]
  rintro ⟨y, v⟩ hy
  have A : f y ∈ (FiberBundle.trivializationAt' (E := E) (F := F) (f x.proj)).baseSet := by
    simpa [trivializationAt, FiberBundle.trivializationAt', Trivialization.pullback] using hy
  simp only [Function.comp_apply, A, lift_pullback_symm_apply]
  rw [Trivialization.apply_symm_apply]
  exact (Trivialization.mk_mem_target (FiberBundle.trivializationAt' (f x.proj))).mpr A

/-- Given a fiber bundle `E` over a manifold `B` and a regular map `f : B' → B`, if `φ` is
a map into the total space of the pullback `f *ᵖ E`, then its regularity can be checked by checking
the regularity of (1) the map `TotalSpace.proj ∘ φ` into `B'`, and (2) the map
`Pullback.lift f ∘ φ` into the total space of `E`. -/
theorem Bundle.Pullback.contMDiff_of_contMDiff_proj_comp_of_contMDiff_lift_comp
    {φ : M → TotalSpace F (f *ᵖ E)} (h1 : ContMDiff IM IB' n (TotalSpace.proj ∘ φ))
    (h2 : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n (Pullback.lift f ∘ φ)) :
    ContMDiff IM (IB'.prod 𝓘(𝕜, F)) n φ := by
  intro x
  have h1_cont : Continuous (TotalSpace.proj ∘ φ) := h1.continuous
  have h2_cont : Continuous (Pullback.lift f ∘ φ) := h2.continuous
  specialize h1 x
  specialize h2 x
  rw [contMDiffAt_iff_target] at h1 h2 ⊢
  constructor
  · exact Pullback.continuous_of_continuous_proj_comp_of_continuous_lift_comp f h1_cont h2_cont
      |>.continuousAt
  apply ContMDiffAt.prodMk_space h1.2
  have (x : EB × F) : ContMDiffAt 𝓘(𝕜, EB × F) 𝓘(𝕜, F) n Prod.snd x := by
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_snd
  exact (this _).comp _ h2.2

/-- Given a fiber bundle `E` over a manifold `B` and a regular map `f : B' → B`, a map `φ`
into the total space of the pullback `f *ᵖ E` is regular if and only if the following two maps are
regular: (1) the map `TotalSpace.proj ∘ φ` into `B'`, and (2) the map `Pullback.lift f ∘ φ` into the
total space of `E`. -/
theorem Bundle.Pullback.contMDiff_iff_contMDiff_proj_comp_and_contMDiff_lift_comp
    (φ : M → TotalSpace F (f *ᵖ E)) :
    ContMDiff IM (IB'.prod 𝓘(𝕜, F)) n φ ↔ (ContMDiff IM IB' n (TotalSpace.proj ∘ φ)
      ∧ ContMDiff IM (IB.prod 𝓘(𝕜, F)) n (Pullback.lift f ∘ φ)) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · exact (Bundle.contMDiff_proj (f *ᵖ E)).comp h
  · exact (Bundle.Pullback.contMDiff_lift F E f).comp h
  · exact Bundle.Pullback.contMDiff_of_contMDiff_proj_comp_of_contMDiff_lift_comp F E f h₁ h₂

variable [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]

/-- For a `C^n` vector bundle `E` over a manifold `B` and a `C^n` map `f : B' → B`, the pullback
vector bundle `f *ᵖ E` is a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.pullback : ContMDiffVectorBundle n F (f *ᵖ E) IB' where
  contMDiffOn_coordChangeL := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((contMDiffOn_coordChangeL e e').comp f.contMDiff.contMDiffOn fun b hb => hb).congr ?_
    rintro b (hb : f b ∈ e.baseSet ∩ e'.baseSet); ext v
    show ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coordChangeL 𝕜 e' (f b)) v
    rw [e.coordChangeL_apply e' hb, (e.pullback f).coordChangeL_apply' _]
    exacts [rfl, hb]
