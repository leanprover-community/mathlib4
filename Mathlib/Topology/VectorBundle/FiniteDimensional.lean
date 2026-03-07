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

open Bundle FiberBundle

lemma VectorBundle.finiteDimensional
    (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
    [NontriviallyNormedField R] [TopologicalSpace B]
    [TopologicalSpace (TotalSpace F E)]
    [NormedAddCommGroup F] [NormedSpace R F] [FiniteDimensional R F]
    [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
    [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]
    (b : B) : FiniteDimensional R (E b) :=
  (trivializationAt F E b).linearEquivAt R b (mem_baseSet_trivializationAt' b)
    |>.symm.finiteDimensional
