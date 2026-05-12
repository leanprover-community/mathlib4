/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Maps.Strict.Basic

variable (E F : Type*) [AddCommMonoid E] [AddCommMonoid F] [TopologicalSpace E]
  [TopologicalSpace F]
variable (𝕜 : Type*) [Field 𝕜] [PartialOrder 𝕜] [Module 𝕜 E] [Module 𝕜 F]
variable (f : E →L[𝕜] F)

open Topology

lemma technical {A : Submodule 𝕜 E} (hA_closed : IsClosed A)
  (hA_fcodim : FiniteDimensional 𝕜 (E ⧸ A)) : IsStrictMap f ↔ True := sorry
