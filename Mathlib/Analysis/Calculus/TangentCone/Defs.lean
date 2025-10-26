/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/

open Filter Set Metric
open scoped Topology Pointwise

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E | ∃ (c : ℕ → 𝕜) (d : ℕ → E),
    (∀ᶠ n in atTop, x + d n ∈ s) ∧
    Tendsto (fun n => ‖c n‖) atTop atTop ∧
    Tendsto (fun n => c n • d n) atTop (𝓝 y) }

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentConeAt : Dense (Submodule.span 𝕜 (tangentConeAt 𝕜 s x) : Set E)
  mem_closure : x ∈ closure s

@[deprecated (since := "2025-04-27")]
alias UniqueDiffWithinAt.dense_tangentCone := UniqueDiffWithinAt.dense_tangentConeAt

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt 𝕜 s x
