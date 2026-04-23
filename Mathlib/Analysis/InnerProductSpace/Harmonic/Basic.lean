/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
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
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods

/-!
# Harmonic Functions

This file defines harmonic functions on real, finite-dimensional, inner product spaces `E`.
-/

@[expose] public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F}
  {x : E} {s t : Set E} {c : ℝ}

open Topology Laplacian

namespace InnerProductSpace

/-!
## Definition
-/

variable (f x) in
/--
Let `E` be a real, finite-dimensional, inner product space and `x` be a point of `E`. A function `f`
on `E` is harmonic at `x` if it is two times continuously `ℝ`-differentiable and if its Laplacian
vanishes in a neighborhood of `x`.
-/
def HarmonicAt := (ContDiffAt ℝ 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

variable (f s) in
/--
Let `E` be a real, finite-dimensional, inner product space and `s` be a subset of `E`. A function
`f` on `E` is harmonic in a neighborhood of `s` if it is harmonic at every point of `s`.
-/
def HarmonicOnNhd := ∀ x ∈ s, HarmonicAt f x

/--
Harmonic functions are two times continuously differentiable.
-/
lemma HarmonicOnNhd.contDiffOn (hf : HarmonicOnNhd f s) : ContDiffOn ℝ 2 f s :=
  fun x hx ↦ (hf x hx).1.contDiffWithinAt

/-!
## Elementary Properties
-/

/--
If two functions agree in a neighborhood of `x`, then one is harmonic at `x` iff so is the other.
-/
theorem harmonicAt_congr_nhds {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplacian_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplacian_congr_nhds h).trans hf.2⟩

/--
If `f` is harmonic at `x`, then it is harmonic at all points in a neighborhood of `x`.
-/
theorem HarmonicAt.eventually {f : E → F} {x : E} (h : HarmonicAt f x) :
    ∀ᶠ y in 𝓝 x, HarmonicAt f y := by
  filter_upwards [h.1.eventually (by simp), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩

/--
Constant functions are harmonic
-/
@[simp] theorem harmonicAt_const (c : F) :
    HarmonicAt (fun _ ↦ c) x := ⟨by fun_prop, by simp⟩

/--
Constant functions are harmonic
-/
@[simp] theorem harmonicOnNhd_const (c : F) :
    HarmonicOnNhd (fun _ ↦ c) s := fun _ _ ↦ by simp

variable (f) in
/--
Harmonicity is an open property.
-/
theorem isOpen_setOf_harmonicAt : IsOpen { x : E | HarmonicAt f x } :=
  isOpen_iff_mem_nhds.2 (fun _ hx ↦ hx.eventually)

/--
If `f` is harmonic in a neighborhood of `s`, it is harmonic in a neighborhood of every subset.
-/
lemma HarmonicOnNhd.mono (h : HarmonicOnNhd f s) (hst : t ⊆ s) :
    HarmonicOnNhd f t := fun x hx ↦ h x (hst hx)

/--
Harmonic functions are continuous.
-/
@[fun_prop] theorem HarmonicOnNhd.continuousOn (h : HarmonicOnNhd f s) :
    ContinuousOn f s :=
  fun x hx ↦ (h x hx).1.continuousAt.continuousWithinAt (s := s)

/-!
## Vector Space Structure
-/

/--
Sums of harmonic functions are harmonic.
-/
theorem HarmonicAt.add (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ + f₂) x := by
  constructor
  · exact h₁.1.add h₂.1
  · filter_upwards [h₁.1.laplacian_add_nhds h₂.1, h₁.2, h₂.2]
    simp_all

/--
Differences of harmonic functions are harmonic.
-/
theorem HarmonicAt.sub (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ - f₂) x := by
  constructor
  · exact h₁.1.sub h₂.1
  · filter_upwards [h₁.1.laplacian_sub_nhds h₂.1, h₁.2, h₂.2]
    simp_all

/--
Sums of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.add (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ + f₂) s := fun x hx ↦ (h₁ x hx).add (h₂ x hx)

/--
Differences of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.sub (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ - f₂) s := fun x hx ↦ (h₁ x hx).sub (h₂ x hx)

/--
The negative of a harmonic function is harmonic.
-/
theorem HarmonicAt.neg (h : HarmonicAt f x) :
    HarmonicAt (-f) x := by
  constructor
  · simpa using h.1.neg
  · filter_upwards [h.2] with x hx
    simp_all [laplacian_neg]

/--
The negative of a harmonic function is harmonic.
-/
theorem HarmonicOnNhd.neg (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (-f) s := fun x hx ↦ (h x hx).neg

/--
Scalar multiples of harmonic functions are harmonic.
-/
theorem HarmonicAt.const_smul (h : HarmonicAt f x) :
    HarmonicAt (c • f) x := by
  constructor
  · exact h.1.const_smul c
  · filter_upwards [laplacian_smul_nhds c h.1, h.2]
    simp_all

/--
Scalar multiples of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.const_smul (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (c • f) s := fun x hx ↦ (h x hx).const_smul

/-!
## Compatibility with Linear Maps
-/

/--
Compositions of continuous `ℝ`-linear maps with harmonic functions are harmonic.
-/
theorem HarmonicAt.comp_CLM (h : HarmonicAt f x) (l : F →L[ℝ] G) :
    HarmonicAt (l ∘ f) x := by
  constructor
  · exact h.1.continuousLinearMap_comp l
  · filter_upwards [h.1.laplacian_CLM_comp_left_nhds (l := l), h.2]
    simp_all

/--
Compositions of continuous linear maps with harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.comp_CLM (h : HarmonicOnNhd f s) (l : F →L[ℝ] G) :
    HarmonicOnNhd (l ∘ f) s := fun x hx ↦ (h x hx).comp_CLM l

/--
Functions are harmonic iff their compositions with continuous linear equivalences are harmonic.
-/
theorem harmonicAt_comp_CLE_iff (l : F ≃L[ℝ] G) :
    HarmonicAt (l ∘ f) x ↔ HarmonicAt f x := by
  constructor <;> intro h
  · simpa [Function.comp_def] using h.comp_CLM l.symm.toContinuousLinearMap
  · exact h.comp_CLM l.toContinuousLinearMap

/--
Functions are harmonic iff their compositions with continuous linear equivalences are harmonic.
-/
theorem harmonicOnNhd_comp_CLE_iff (l : F ≃L[ℝ] G) :
    HarmonicOnNhd (l ∘ f) s ↔ HarmonicOnNhd f s :=
  forall₂_congr fun _ _ ↦ harmonicAt_comp_CLE_iff l

end InnerProductSpace
