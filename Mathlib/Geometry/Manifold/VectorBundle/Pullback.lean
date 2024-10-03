/-
Copyright (c) 2023 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! # Pullbacks of smooth vector bundles

This file defines pullbacks of smooth vector bundles over a smooth manifold.

## Main definitions

* `SmoothVectorBundle.pullback`: For a smooth vector bundle `E` over a manifold `B` and a smooth
  map `f : B' → B`, the pullback vector bundle `f *ᵖ E` is a smooth vector bundle.

-/

open Bundle Set
open scoped Manifold

variable {𝕜 B B' : Type*} (F : Type*) (E : B → Type*)
variable [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B]
  [ChartedSpace HB B] [SmoothManifoldWithCorners IB B] {EB' : Type*} [NormedAddCommGroup EB']
  [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB'] (IB' : ModelWithCorners 𝕜 EB' HB')
  [TopologicalSpace B'] [ChartedSpace HB' B'] [SmoothManifoldWithCorners IB' B'] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [SmoothVectorBundle F E IB] (f : SmoothMap IB' IB B' B)

/-- For a smooth vector bundle `E` over a manifold `B` and a smooth map `f : B' → B`, the pullback
vector bundle `f *ᵖ E` is a smooth vector bundle. -/
instance SmoothVectorBundle.pullback : SmoothVectorBundle F (f *ᵖ E) IB' where
  smoothOn_coordChangeL := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((smoothOn_coordChangeL _ e e').comp f.smooth.smoothOn fun b hb => hb).congr ?_
    rintro b (hb : f b ∈ e.baseSet ∩ e'.baseSet); ext v
    show ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coordChangeL 𝕜 e' (f b)) v
    rw [e.coordChangeL_apply e' hb, (e.pullback f).coordChangeL_apply' _]
    exacts [rfl, hb]

/-- For a smooth vector bundle `E` over a manifold `B` and a smooth map `f : B' → B`, the natural
"lift" map from the total space of `f *ᵖ E` to the total space of `E` is smooth. -/
theorem Bundle.Pullback.smooth_lift :
    Smooth (IB'.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (Pullback.lift f : TotalSpace F (f *ᵖ E) → _) := by
  sorry

variable {M EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [SmoothManifoldWithCorners IM M]

/-- Given a smooth vector bundle `E` over a manifold `B` and a smooth map `f : B' → B`, if `φ` is
a map into the total space of the pullback `f *ᵖ E`, then its smoothness can be checked by checking
the smoothness of (1) the map `TotalSpace.proj ∘ φ` into `B'`, and (ii) the map
`Pullback.lift f ∘ φ` into the total space of `E`. -/
theorem Bundle.Pullback.smooth_of_smooth_proj_comp_of_smooth_lift_comp
    {φ : M → TotalSpace F (f *ᵖ E)} (h1 : Smooth IM IB' (TotalSpace.proj ∘ φ))
    (h2 : Smooth IM (IB.prod 𝓘(𝕜, F)) (Pullback.lift f ∘ φ)) : Smooth IM (IB'.prod 𝓘(𝕜, F)) φ := by
  sorry
