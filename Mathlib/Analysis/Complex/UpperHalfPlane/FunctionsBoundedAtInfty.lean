/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler

! This file was ported from Lean 3 source module analysis.complex.upper_half_plane.functions_bounded_at_infty
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Bounded at infinity

For complex valued functions on the upper half plane, this file defines the filter `atImInfty`
required for defining when functions are bounded at infinity and zero at infinity.
Both of which are relevant for defining modular forms.

-/


open Complex Filter

open scoped Topology UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- Filter for approaching `i∞`. -/
def atImInfty :=
  Filter.atTop.comap UpperHalfPlane.im
#align upper_half_plane.at_im_infty UpperHalfPlane.atImInfty

theorem atImInfty_basis : atImInfty.HasBasis (fun _ => True) fun i : ℝ => im ⁻¹' Set.Ici i :=
  Filter.HasBasis.comap UpperHalfPlane.im Filter.atTop_basis
#align upper_half_plane.at_im_infty_basis UpperHalfPlane.atImInfty_basis

theorem atImInfty_mem (S : Set ℍ) : S ∈ atImInfty ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S := by
  simp only [atImInfty, Filter.mem_comap', Filter.mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq,
    UpperHalfPlane.coe_im]
  refine' ⟨fun ⟨a, h⟩ => ⟨a, fun z hz => h (im z) hz rfl⟩, _⟩
  rintro ⟨A, h⟩
  refine' ⟨A, fun b hb x hx => h x _⟩
  rwa [hx]
#align upper_half_plane.at_im_infty_mem UpperHalfPlane.atImInfty_mem

/-- A function ` f : ℍ → α` is bounded at infinity if it is bounded along `atImInfty`. -/
def IsBoundedAtImInfty {α : Type _} [Norm α] (f : ℍ → α) : Prop :=
  BoundedAtFilter atImInfty f
#align upper_half_plane.is_bounded_at_im_infty UpperHalfPlane.IsBoundedAtImInfty

/-- A function ` f : ℍ → α` is zero at infinity it is zero along `atImInfty`. -/
def IsZeroAtImInfty {α : Type _} [Zero α] [TopologicalSpace α] (f : ℍ → α) : Prop :=
  ZeroAtFilter atImInfty f
#align upper_half_plane.is_zero_at_im_infty UpperHalfPlane.IsZeroAtImInfty

theorem zero_form_isBoundedAtImInfty {α : Type _} [NormedField α] :
    IsBoundedAtImInfty (0 : ℍ → α) :=
  const_boundedAtFilter atImInfty (0 : α)
#align upper_half_plane.zero_form_is_bounded_at_im_infty UpperHalfPlane.zero_form_isBoundedAtImInfty

/-- Module of functions that are zero at infinity. -/
def zeroAtImInftySubmodule (α : Type _) [NormedField α] : Submodule α (ℍ → α) :=
  zeroAtFilterSubmodule atImInfty
#align upper_half_plane.zero_at_im_infty_submodule UpperHalfPlane.zeroAtImInftySubmodule

/-- Subalgebra of functions that are bounded at infinity. -/
def boundedAtImInftySubalgebra (α : Type _) [NormedField α] : Subalgebra α (ℍ → α) :=
  boundedFilterSubalgebra atImInfty
#align upper_half_plane.bounded_at_im_infty_subalgebra UpperHalfPlane.boundedAtImInftySubalgebra

nonrec theorem IsBoundedAtImInfty.mul {f g : ℍ → ℂ} (hf : IsBoundedAtImInfty f)
    (hg : IsBoundedAtImInfty g) : IsBoundedAtImInfty (f * g) := by
  simpa only [Pi.one_apply, mul_one, norm_eq_abs] using hf.mul hg
#align upper_half_plane.is_bounded_at_im_infty.mul UpperHalfPlane.IsBoundedAtImInfty.mul

theorem bounded_mem (f : ℍ → ℂ) :
    IsBoundedAtImInfty f ↔ ∃ M A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M := by
  simp [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, Filter.Eventually,
    atImInfty_mem]
#align upper_half_plane.bounded_mem UpperHalfPlane.bounded_mem

theorem zero_at_im_infty (f : ℍ → ℂ) :
    IsZeroAtImInfty f ↔ ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ ε := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_iff_forall_eventually_mem]
  constructor
  · simp_rw [Filter.Eventually, atImInfty_mem]
    intro h ε hε
    simpa using h (Metric.closedBall (0 : ℂ) ε) (Metric.closedBall_mem_nhds (0 : ℂ) hε)
  · simp_rw [Metric.mem_nhds_iff]
    intro h s hs
    simp_rw [Filter.Eventually, atImInfty_mem]
    obtain ⟨ε, h1, h2⟩ := hs
    have h11 : 0 < ε / 2 := by linarith
    obtain ⟨A, hA⟩ := h (ε / 2) h11
    use A
    intro z hz
    have hzs : f z ∈ s := by
      apply h2
      simp only [mem_ball_zero_iff, norm_eq_abs]
      apply lt_of_le_of_lt (hA z hz)
      linarith
    apply hzs
#align upper_half_plane.zero_at_im_infty UpperHalfPlane.zero_at_im_infty

end UpperHalfPlane
