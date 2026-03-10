/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite-rank vector bundles -/

@[expose] public section

namespace VectorBundle

open Bundle FiberBundle

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]

include E F

protected lemma finiteDimensional (b : B) [FiniteDimensional R F] : FiniteDimensional R (E b) :=
  (continuousLinearEquivAt R F E b).symm.finiteDimensional

protected lemma finrank_eq (b : B) : Module.finrank R (E b) = Module.finrank R F :=
  (continuousLinearEquivAt R F E b).finrank_eq

end VectorBundle
