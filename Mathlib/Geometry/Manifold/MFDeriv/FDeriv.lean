/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Init
import Mathlib.Tactic.AdaptationNote
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Fréchet derivative `fderiv`. In this section, we prove
this and related statements.
-/

public section

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

section MFDerivFDeriv

theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffWithinAt 𝓘(𝕜, E) s x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=
  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt

theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiffOn 𝓘(𝕜, E) s ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn

theorem ModelWithCorners.uniqueMDiffOn {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : UniqueMDiffOn 𝓘(𝕜, E) (Set.range I) :=
  I.uniqueDiffOn.uniqueMDiffOn

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about this being `@[simp]`. -/
@[mfld_simps]
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl

theorem hasMFDerivWithinAt_iff_hasFDerivWithinAt {f'} :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' ↔ HasFDerivWithinAt f f' s x := by
  simpa only [HasMFDerivWithinAt, and_iff_right_iff_imp, mfld_simps] using
    HasFDerivWithinAt.continuousWithinAt

alias ⟨HasMFDerivWithinAt.hasFDerivWithinAt, HasFDerivWithinAt.hasMFDerivWithinAt⟩ :=
  hasMFDerivWithinAt_iff_hasFDerivWithinAt

theorem hasMFDerivAt_iff_hasFDerivAt {f'} :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ HasFDerivAt f f' x := by
  rw [← hasMFDerivWithinAt_univ, hasMFDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_univ]

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt

/-- For maps between vector spaces, `MDifferentiableWithinAt` and `DifferentiableWithinAt`
coincide -/
theorem mdifferentiableWithinAt_iff_differentiableWithinAt :
    MDiffAt[s] f x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [mdifferentiableWithinAt_iff', mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousWithinAt, H⟩⟩

alias ⟨MDifferentiableWithinAt.differentiableWithinAt,
    DifferentiableWithinAt.mdifferentiableWithinAt⟩ :=
  mdifferentiableWithinAt_iff_differentiableWithinAt

/-- For maps between vector spaces, `MDifferentiableAt` and `DifferentiableAt` coincide -/
theorem mdifferentiableAt_iff_differentiableAt :
    MDiffAt f x ↔ DifferentiableAt 𝕜 f x := by
  simp only [mdifferentiableAt_iff, differentiableWithinAt_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousAt, H⟩⟩

alias ⟨MDifferentiableAt.differentiableAt, DifferentiableAt.mdifferentiableAt⟩ :=
  mdifferentiableAt_iff_differentiableAt

/-- For maps between vector spaces, `MDifferentiableOn` and `DifferentiableOn` coincide -/
theorem mdifferentiableOn_iff_differentiableOn :
    MDiff[s] f ↔ DifferentiableOn 𝕜 f s := by
  simp only [MDifferentiableOn, DifferentiableOn,
    mdifferentiableWithinAt_iff_differentiableWithinAt]

alias ⟨MDifferentiableOn.differentiableOn, DifferentiableOn.mdifferentiableOn⟩ :=
  mdifferentiableOn_iff_differentiableOn

/-- For maps between vector spaces, `MDifferentiable` and `Differentiable` coincide -/
theorem mdifferentiable_iff_differentiable : MDiff f ↔ Differentiable 𝕜 f := by
  simp only [MDifferentiable, Differentiable, mdifferentiableAt_iff_differentiableAt]

alias ⟨MDifferentiable.differentiable, Differentiable.mdifferentiable⟩ :=
  mdifferentiable_iff_differentiable

/-- For maps between vector spaces, `mfderivWithin` and `fderivWithin` coincide -/
@[simp]
theorem mfderivWithin_eq_fderivWithin :
    mfderiv[s] f x = fderivWithin 𝕜 f s x := by
  by_cases h : MDiffAt[s] f x
  · simp only [mfderivWithin, h, if_pos, mfld_simps]
  · simp only [mfderivWithin, h, if_neg, not_false_iff]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at h
    exact (fderivWithin_zero_of_not_differentiableWithinAt h).symm

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp]
theorem mfderiv_eq_fderiv : mfderiv% f x = fderiv 𝕜 f x := by
  rw [← mfderivWithin_univ, ← fderivWithin_univ]
  exact mfderivWithin_eq_fderivWithin

end MFDerivFDeriv
