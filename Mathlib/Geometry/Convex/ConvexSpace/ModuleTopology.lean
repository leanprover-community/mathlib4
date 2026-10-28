/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Continuity of affine maps from the standard simplex to modules

-/

open Topology

namespace Convexity.StdSimplex

variable {R E ι : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [ConvexSpace R E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace R]
  [IsTopologicalRing R] [ContinuousSMul R E] [IsModuleConvexSpace R E]

@[fun_prop]
public lemma continuous_of_affineMap (f : ConvexSpace.AffineMap R (StdSimplex R ι) E) :
    Continuous f := by
  wlog hι : Finite ι generalizing ι
  · rw [StdSimplex.continuous_iff]
    intro ι' _ g
    exact this (f.comp (affineMap g)) inferInstance
  have := Fintype.ofFinite ι
  obtain ⟨f, rfl⟩ := StdSimplex.affineMapMk_surjective f
  rw [StdSimplex.coe_affineMapMk_of_fintype]
  fun_prop

public lemma continuous_of_isAffineMap (f : StdSimplex R ι → E) (hf : IsAffineMap R f) :
    Continuous f :=
  continuous_of_affineMap ⟨f, hf⟩

end Convexity.StdSimplex
