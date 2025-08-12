/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Harmonic Functions

This file defines harmonic functions on real, finite-dimensional, inner product spaces `E`.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F}
  {x : E} {s t : Set E} {c : ℝ}

open Topology

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
Sums of harmonic functions are harmonic.
-/
theorem HarmonicOnNhd.add (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ + f₂) s := fun x hx ↦ (h₁ x hx).add (h₂ x hx)

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
