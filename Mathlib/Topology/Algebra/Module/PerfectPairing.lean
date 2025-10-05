/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Continuous perfect pairings

This file defines continuous perfect pairings.

For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing is
a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several different topologies
on the continuous dual (e.g., strong, weak, weak-*). For example, if `M` is weakly reflexive then
there is a continuous perfect pairing between `M` and `WeakDual R M`, even though the map
`WeakDual R M ≃ₗ[R] StrongDual R M` (where `StrongDual R M` is equipped with its strong topology) is
not in general a homeomorphism.

## TODO

Adapt `PerfectPairing` to this Prop-valued typeclass paradigm
-/

open Function

namespace LinearMap
variable {R M N : Type*}
  [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] (p : M →ₗ[R] N →ₗ[R] R) {x : M} {y : N}

/-- For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing
is a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several different topologies
on the continuous dual: strong, weak, weak-* topology... -/
@[ext]
class IsContPerfPair (p : M →ₗ[R] N →ₗ[R] R) where
  continuous_uncurry (p) : Continuous fun (x, y) ↦ p x y
  bijective_left (p) :
    Bijective fun x ↦ ContinuousLinearMap.mk (p x) <| continuous_uncurry.comp <| .prodMk_right x
  bijective_right (p) :
    Bijective fun y ↦ ContinuousLinearMap.mk (p.flip y) <| continuous_uncurry.comp <| .prodMk_left y

variable [p.IsContPerfPair]

alias continuous_uncurry_of_isContPerfPair :=
  IsContPerfPair.continuous_uncurry

/-- Given a perfect pairing between `M`and `N`, we may interchange the roles of `M` and `N`. -/
instance flip.instIsContPerfPair : p.flip.IsContPerfPair where
  continuous_uncurry := p.continuous_uncurry_of_isContPerfPair.comp continuous_swap
  bijective_left := IsContPerfPair.bijective_right p
  bijective_right := IsContPerfPair.bijective_left p

lemma continuous_of_isContPerfPair : Continuous (p x) :=
  p.continuous_uncurry_of_isContPerfPair.comp <| .prodMk_right x

variable [IsTopologicalRing R]

/-- Turn a continuous perfect pairing between `M` and `N` into a map from `M` to continuous linear
maps `N → R`. -/
noncomputable def toContPerfPair : M ≃ₗ[R] StrongDual R N :=
  .ofBijective { toFun := _, map_add' x y := by ext; simp, map_smul' r x := by ext; simp } <|
    IsContPerfPair.bijective_left p

@[simp] lemma toLinearMap_toContPerfPair (x : M) : p.toContPerfPair x = p x := rfl
@[simp] lemma toContPerfPair_apply (x : M) (y : N) : p.toContPerfPair x y = p x y := rfl

end LinearMap
