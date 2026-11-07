/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.FiberBundle.SecToFun

import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Lemmas about `funToSec` and `secToFun` in smooth vector bundles

TODO: move the remaining lemmas which belong here to this file
-/

public section

open Topology
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]
  {e : Trivialization F (π F V)} [MemTrivializationAtlas e]
  {x : M} {s : M → F} {σ : (x : M) → V x}

section

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
variable (e)

lemma mdifferentiableAt_funToSec (hx : x ∈ e.baseSet) (hs : MDiffAt s x) :
    MDiffAt (T% (e.funToSec s)) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx]
  change MDiffAt (e.secToFun <| e.funToSec s) x
  have := e.secToFun_funToSec_eventuallyEq hx s
  exact hs.congr_of_eventuallyEq this

lemma mdifferentiableAt_funToSec' (hx : x ∈ e.baseSet) (hs : MDiffAt (T% s) x) :
    MDiffAt (T% (e.funToSec s)) x := by
  rw [mdifferentiableAt_total_trivial_iff] at hs
  apply mdifferentiableAt_funToSec _ hx hs

lemma mdifferentiableAt_secToFun (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) :
    MDiffAt (e.secToFun σ) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx] at hσ
  exact hσ

lemma mdifferentiableAt_total_secToFun (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) :
    MDiffAt (T% (e.secToFun σ)) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx] at hσ
  exact (mdifferentiableAt_section I _).mpr hσ

end

omit [MemTrivializationAtlas e] [∀ x, Module 𝕜 (V x)] in
@[simp]
lemma mdifferentiableAt_total_funToSec_secToFun (hx : x ∈ e.baseSet) :
    MDiffAt (T% (e.funToSec <| e.secToFun σ)) x ↔ MDiffAt (T%σ) x := by
  rw [e.total_funToSec_secToFun_eventuallyEq hx σ |>.mdifferentiableAt_iff]

omit [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [MemTrivializationAtlas e] in
@[simp]
lemma mdifferentiableAt_secToFun_funToSec (hx : x ∈ e.baseSet) :
    MDiffAt (e.secToFun <| e.funToSec s) x ↔ MDiffAt s x :=
  e.secToFun_funToSec_eventuallyEq hx s |>.mdifferentiableAt_iff

end Bundle.Trivialization
