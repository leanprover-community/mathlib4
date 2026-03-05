/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation

/-!
# Locally extending an element of a vector bundle to a smooth section

Unlike the other `extend`, this construction doesn't use bump functions, just extends naively on a
trivialization's domain.

-/

public section

open Bundle Filter Module Topology Set
open scoped Manifold ContDiff

section extend

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F]
  -- `F` model fiber
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]
  -- `V` vector bundle

open Classical in
/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
-/
noncomputable def extend {x : M} (v₀ : V x) :
    (x' : M) → V x' :=
  letI t := trivializationAt F V x
  letI w : F := (t ⟨x, v₀⟩).2
  fun x' ↦ t.symm x' w

variable {I F} in
@[simp] lemma extend_apply_self {x : M} (v : V x) :
    extend F v x = v := by
  unfold extend
  simp [FiberBundle.mem_baseSet_trivializationAt' x]

variable [NormedSpace 𝕜 F]

-- TODO there is a lemma already with this name which should be renamed to something like
-- `Chart.contMDiffAt_extend` or `OpenPartialHomeomorph.contMDiffAt_extend`
lemma contMDiffAt_extend' {k} [IsManifold I k M] {x : M} (σ₀ : V x) :
    CMDiffAt k (T% (extend F σ₀)) x := by
  rw [contMDiffAt_section]
  set t := trivializationAt F V x
  let w : F := (t ⟨x, σ₀⟩).2
  have : CMDiffAt k (fun (_x : M) ↦ w) x := contMDiffAt_const
  refine this.congr_of_eventuallyEq ?_
  apply eventually_nhds_iff.mpr
  refine ⟨t.baseSet, ?_, t.open_baseSet, ?_⟩
  · intro x hx
    dsimp only
    unfold extend
    simp [t, hx, w]
  · exact FiberBundle.mem_baseSet_trivializationAt' x

lemma mdifferentiableAt_extend [IsManifold I 1 M] {x : M} (σ₀ : V x) :
    MDiffAt (T% (extend F σ₀)) x :=
  have := contMDiffAt_extend' (k := 1) I F σ₀
  this.mdifferentiableAt one_ne_zero

-- TODO also prove `ContMDiffOn` and `MDifferentiableOn` in a neighbourhood of the point

end extend
