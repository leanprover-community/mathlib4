/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Bounded at infinity

For complex valued functions on the upper half plane, this file defines the filter
`UpperHalfPlane.atImInfty` required for defining when functions are bounded at infinity and zero at
infinity. Both of which are relevant for defining modular forms.
-/

open Complex Filter

open scoped Topology UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- Filter for approaching `i∞`. -/
def atImInfty :=
  Filter.atTop.comap UpperHalfPlane.im

theorem atImInfty_basis : atImInfty.HasBasis (fun _ => True) fun i : ℝ => im ⁻¹' Set.Ici i :=
  Filter.HasBasis.comap UpperHalfPlane.im Filter.atTop_basis

theorem atImInfty_mem (S : Set ℍ) : S ∈ atImInfty ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S := by
  simp only [atImInfty_basis.mem_iff, true_and]; rfl

/-- A function `f : ℍ → α` is bounded at infinity if it is bounded along `atImInfty`. -/
def IsBoundedAtImInfty {α : Type*} [Norm α] (f : ℍ → α) : Prop :=
  BoundedAtFilter atImInfty f

/-- A function `f : ℍ → α` is zero at infinity it is zero along `atImInfty`. -/
def IsZeroAtImInfty {α : Type*} [Zero α] [TopologicalSpace α] (f : ℍ → α) : Prop :=
  ZeroAtFilter atImInfty f

theorem zero_form_isBoundedAtImInfty {α : Type*} [NormedField α] :
    IsBoundedAtImInfty (0 : ℍ → α) :=
  const_boundedAtFilter atImInfty (0 : α)

/-- Module of functions that are zero at infinity. -/
def zeroAtImInftySubmodule (α : Type*) [NormedField α] : Submodule α (ℍ → α) :=
  zeroAtFilterSubmodule _ atImInfty

/-- Subalgebra of functions that are bounded at infinity. -/
def boundedAtImInftySubalgebra (α : Type*) [NormedField α] : Subalgebra α (ℍ → α) :=
  boundedFilterSubalgebra _ atImInfty

nonrec theorem IsBoundedAtImInfty.mul {f g : ℍ → ℂ} (hf : IsBoundedAtImInfty f)
    (hg : IsBoundedAtImInfty g) : IsBoundedAtImInfty (f * g) := by
  simpa only [Pi.one_apply, mul_one, norm_eq_abs] using hf.mul hg

theorem bounded_mem (f : ℍ → ℂ) :
    IsBoundedAtImInfty f ↔ ∃ M A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M := by
  simp [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, Filter.Eventually,
    atImInfty_mem]

theorem zero_at_im_infty (f : ℍ → ℂ) :
    IsZeroAtImInfty f ↔ ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ ε :=
  (atImInfty_basis.tendsto_iff Metric.nhds_basis_closedBall).trans <| by
    simp only [true_and, mem_closedBall_zero_iff]; rfl

end UpperHalfPlane
