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
open scoped Manifold

variable {𝕜 B B' : Type*} (F : Type*) (E : B → Type*) {n : WithTop ℕ∞}
variable [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EB' : Type*} [NormedAddCommGroup EB']
  [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB'] (IB' : ModelWithCorners 𝕜 EB' HB')
  [TopologicalSpace B'] [ChartedSpace HB' B'] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB] (f : ContMDiffMap IB' IB B' B n)

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

variable {IB'}

/-- For a smooth vector bundle `E` over a manifold `B` and a smooth map `f : B' → B`, the natural
"lift" map from the total space of `f *ᵖ E` to the total space of `E` is smooth. -/
theorem Bundle.Pullback.smooth_lift :
    Smooth (IB'.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (Pullback.lift f : TotalSpace F (f *ᵖ E) → _) := by
  intro x
  rw [contMDiffAt_totalSpace]
  refine ⟨f.smooth.smoothAt.comp _ (smoothAt_proj (f *ᵖ E)), ?_⟩
  refine (contMDiffAt_snd (M := B')).comp _ <|
    (smoothOn_trivializationAt x).contMDiffAt ?_
  apply (trivializationAt F (f *ᵖ E) x.proj).open_source.mem_nhds
  simp

variable {M EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]

omit [(x : B) → Module 𝕜 (E x)] in
/-- Given a smooth fibre bundle `E` over a manifold `B` and a smooth map `f : B' → B`, if `φ` is
a map into the total space of the pullback `f *ᵖ E`, then its smoothness can be checked by checking
the smoothness of (1) the map `TotalSpace.proj ∘ φ` into `B'`, and (2) the map
`Pullback.lift f ∘ φ` into the total space of `E`. -/
theorem Bundle.Pullback.smooth_of_smooth_proj_comp_of_smooth_lift_comp
    {φ : M → TotalSpace F (f *ᵖ E)} (h1 : Smooth IM IB' (TotalSpace.proj ∘ φ))
    (h2 : Smooth IM (IB.prod 𝓘(𝕜, F)) (Pullback.lift f ∘ φ)) : Smooth IM (IB'.prod 𝓘(𝕜, F)) φ := by
  intro x
  have h1_cont : Continuous (TotalSpace.proj ∘ φ) := h1.continuous
  have h2_cont : Continuous (Pullback.lift f ∘ φ) := h2.continuous
  specialize h1 x
  specialize h2 x
  rw [contMDiffAt_iff_target] at h1 h2 ⊢
  constructor
  · exact Pullback.continuous_of_continuous_proj_comp_of_smooth_lift_comp f h1_cont h2_cont
      |>.continuousAt
  apply ContMDiffAt.prod_mk_space h1.2
  have (x : EB × F) : ContMDiffAt 𝓘(𝕜, EB × F) 𝓘(𝕜, F) ⊤ Prod.snd x := by
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_snd
  exact (this _).comp _ h2.2

/-- Given a smooth fibre bundle `E` over a manifold `B` and a smooth map `f : B' → B`, a map `φ`
into the total space of the pullback `f *ᵖ E` is smooth if and only if the following two maps are
smooth: (1) the map `TotalSpace.proj ∘ φ` into `B'`, and (2) the map `Pullback.lift f ∘ φ` into the
total space of `E`. -/
theorem Bundle.Pullback.smooth_iff_smooth_proj_comp_and_smooth_lift_comp
    (φ : M → TotalSpace F (f *ᵖ E)) :
    Smooth IM (IB'.prod 𝓘(𝕜, F)) φ ↔
    (Smooth IM IB' (TotalSpace.proj ∘ φ) ∧ Smooth IM (IB.prod 𝓘(𝕜, F)) (Pullback.lift f ∘ φ)) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · exact (Bundle.smooth_proj (f *ᵖ E)).comp h
  · exact (Bundle.Pullback.smooth_lift F E f).comp h
  · exact Bundle.Pullback.smooth_of_smooth_proj_comp_of_smooth_lift_comp F E f h₁ h₂
