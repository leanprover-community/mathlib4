/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Monoid

/-!
# Continuity of the functoriality of `X → M` when `X` is finite

-/

public section

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
