/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Topology.Algebra.Monoid
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Continuity of the functoriality of `X → M` when `X` is finite

-/

namespace FunOnFinite

lemma continuous_map
    (M : Type*) [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) :
    Continuous (FunOnFinite.map (M := M) f) := by
  classical
  have := Fintype.ofFinite X
  refine continuous_pi (fun y ↦ ?_)
  simp only [FunOnFinite.map_apply_apply]
  exact continuous_finset_sum _ (fun _ _ ↦ continuous_apply _)

lemma continuous_linearMap
    (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) :
    Continuous (FunOnFinite.linearMap R M f) :=
  FunOnFinite.continuous_map _ _

end FunOnFinite
