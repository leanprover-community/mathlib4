/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Frechet derivative `fderiv`. In this section, we prove
this and related statements.
-/

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

section MFDerivFderiv

theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffWithinAt 𝓘(𝕜, E) s x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]
#align unique_mdiff_within_at_iff_unique_diff_within_at uniqueMDiffWithinAt_iff_uniqueDiffWithinAt

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=
  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt
#align unique_mdiff_within_at.unique_diff_within_at UniqueMDiffWithinAt.uniqueDiffWithinAt
#align unique_diff_within_at.unique_mdiff_within_at UniqueDiffWithinAt.uniqueMDiffWithinAt

theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiffOn 𝓘(𝕜, E) s ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
#align unique_mdiff_on_iff_unique_diff_on uniqueMDiffOn_iff_uniqueDiffOn

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn
#align unique_mdiff_on.unique_diff_on UniqueMDiffOn.uniqueDiffOn
#align unique_diff_on.unique_mdiff_on UniqueDiffOn.uniqueMDiffOn

-- Porting note (#10618): was `@[simp, mfld_simps]` but `simp` can prove it
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl
#align written_in_ext_chart_model_space writtenInExtChartAt_model_space

theorem hasMFDerivWithinAt_iff_hasFDerivWithinAt {f'} :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' ↔ HasFDerivWithinAt f f' s x := by
  simpa only [HasMFDerivWithinAt, and_iff_right_iff_imp, mfld_simps] using
    HasFDerivWithinAt.continuousWithinAt
#align has_mfderiv_within_at_iff_has_fderiv_within_at hasMFDerivWithinAt_iff_hasFDerivWithinAt

alias ⟨HasMFDerivWithinAt.hasFDerivWithinAt, HasFDerivWithinAt.hasMFDerivWithinAt⟩ :=
  hasMFDerivWithinAt_iff_hasFDerivWithinAt
#align has_mfderiv_within_at.has_fderiv_within_at HasMFDerivWithinAt.hasFDerivWithinAt
#align has_fderiv_within_at.has_mfderiv_within_at HasFDerivWithinAt.hasMFDerivWithinAt

theorem hasMFDerivAt_iff_hasFDerivAt {f'} :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ HasFDerivAt f f' x := by
  rw [← hasMFDerivWithinAt_univ, hasMFDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_univ]
#align has_mfderiv_at_iff_has_fderiv_at hasMFDerivAt_iff_hasFDerivAt

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt
#align has_mfderiv_at.has_fderiv_at HasMFDerivAt.hasFDerivAt
#align has_fderiv_at.has_mfderiv_at HasFDerivAt.hasMFDerivAt

/-- For maps between vector spaces, `MDifferentiableWithinAt` and `DifferentiableWithinAt`
coincide -/
theorem mdifferentiableWithinAt_iff_differentiableWithinAt :
    MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [mdifferentiableWithinAt_iff', mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousWithinAt, H⟩⟩
#align mdifferentiable_within_at_iff_differentiable_within_at mdifferentiableWithinAt_iff_differentiableWithinAt

alias ⟨MDifferentiableWithinAt.differentiableWithinAt,
    DifferentiableWithinAt.mdifferentiableWithinAt⟩ :=
  mdifferentiableWithinAt_iff_differentiableWithinAt
#align mdifferentiable_within_at.differentiable_within_at MDifferentiableWithinAt.differentiableWithinAt
#align differentiable_within_at.mdifferentiable_within_at DifferentiableWithinAt.mdifferentiableWithinAt

/-- For maps between vector spaces, `MDifferentiableAt` and `DifferentiableAt` coincide -/
theorem mdifferentiableAt_iff_differentiableAt :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x ↔ DifferentiableAt 𝕜 f x := by
  simp only [mdifferentiableAt_iff, differentiableWithinAt_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousAt, H⟩⟩
#align mdifferentiable_at_iff_differentiable_at mdifferentiableAt_iff_differentiableAt

alias ⟨MDifferentiableAt.differentiableAt, DifferentiableAt.mdifferentiableAt⟩ :=
  mdifferentiableAt_iff_differentiableAt
#align mdifferentiable_at.differentiable_at MDifferentiableAt.differentiableAt
#align differentiable_at.mdifferentiable_at DifferentiableAt.mdifferentiableAt

/-- For maps between vector spaces, `MDifferentiableOn` and `DifferentiableOn` coincide -/
theorem mdifferentiableOn_iff_differentiableOn :
    MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s ↔ DifferentiableOn 𝕜 f s := by
  simp only [MDifferentiableOn, DifferentiableOn,
    mdifferentiableWithinAt_iff_differentiableWithinAt]
#align mdifferentiable_on_iff_differentiable_on mdifferentiableOn_iff_differentiableOn

alias ⟨MDifferentiableOn.differentiableOn, DifferentiableOn.mdifferentiableOn⟩ :=
  mdifferentiableOn_iff_differentiableOn
#align mdifferentiable_on.differentiable_on MDifferentiableOn.differentiableOn
#align differentiable_on.mdifferentiable_on DifferentiableOn.mdifferentiableOn

/-- For maps between vector spaces, `MDifferentiable` and `Differentiable` coincide -/
theorem mdifferentiable_iff_differentiable :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f ↔ Differentiable 𝕜 f := by
  simp only [MDifferentiable, Differentiable, mdifferentiableAt_iff_differentiableAt]
#align mdifferentiable_iff_differentiable mdifferentiable_iff_differentiable

alias ⟨MDifferentiable.differentiable, Differentiable.mdifferentiable⟩ :=
  mdifferentiable_iff_differentiable
#align mdifferentiable.differentiable MDifferentiable.differentiable
#align differentiable.mdifferentiable Differentiable.mdifferentiable

/-- For maps between vector spaces, `mfderivWithin` and `fderivWithin` coincide -/
@[simp]
theorem mfderivWithin_eq_fderivWithin :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = fderivWithin 𝕜 f s x := by
  by_cases h : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
  · simp only [mfderivWithin, h, if_pos, mfld_simps]
  · simp only [mfderivWithin, h, if_neg, not_false_iff]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at h
    exact (fderivWithin_zero_of_not_differentiableWithinAt h).symm
#align mfderiv_within_eq_fderiv_within mfderivWithin_eq_fderivWithin

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp]
theorem mfderiv_eq_fderiv : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = fderiv 𝕜 f x := by
  rw [← mfderivWithin_univ, ← fderivWithin_univ]
  exact mfderivWithin_eq_fderivWithin
#align mfderiv_eq_fderiv mfderiv_eq_fderiv

end MFDerivFderiv
