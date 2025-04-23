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

Note that this does **not** imply that the dual of `M` is `N` and vice-versa (one would instead need
"homeomorphic in both arguments").
-/

open Function

variable {R M N : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

variable (R M N) in
/-- For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing
is a continuous bilinear map `M × N → R` that is bijective in both arguments.

Note that this does **not** imply that the dual of `M` is `N` and vice-versa (one would instead need
"homeomorphic in both arguments"). -/
@[ext]
structure ContinuousPerfectPairing extends M →ₗ[R] N →ₗ[R] R where
  continuous_uncurry : Continuous fun (x, y) ↦ toLinearMap x y
  bijective_left' :
    Bijective fun x ↦
      ContinuousLinearMap.mk (toLinearMap x) <| continuous_uncurry.comp <| .prodMk_right x
  bijective_right' :
    Bijective fun y ↦
      ContinuousLinearMap.mk (toLinearMap.flip y) <| continuous_uncurry.comp <| .prodMk_left y

namespace ContinuousPerfectPairing
variable {p : ContinuousPerfectPairing R M N} {x : M} {y : N}

lemma toLinearMap_injective :
    Injective (toLinearMap : ContinuousPerfectPairing R M N → M →ₗ[R] N →ₗ[R] R) := by
  rintro ⟨p⟩ ⟨q⟩ rfl; rfl

variable (p) in
lemma continuous_toLinearMap_left : Continuous (p.toLinearMap x) :=
  p.continuous_uncurry.comp <| .prodMk_right x

variable (p) in
lemma continuous_toLinearMap_right : Continuous (p.toLinearMap.flip y) :=
  p.continuous_uncurry.comp <| .prodMk_left y

instance : FunLike (ContinuousPerfectPairing R M N) M (N →L[R] R) where
  coe p x := ContinuousLinearMap.mk (p.toLinearMap x) p.continuous_toLinearMap_left
  coe_injective' p q h := by ext x : 2; dsimp at h; exact congr(($h x).toLinearMap)

instance : ZeroHomClass (ContinuousPerfectPairing R M N) M (N →L[R] R) where
  map_zero p := ContinuousLinearMap.coe_injective p.toLinearMap.map_zero

instance [ContinuousAdd R] : AddMonoidHomClass (ContinuousPerfectPairing R M N) M (N →L[R] R) where
  map_add p x y := ContinuousLinearMap.coe_injective <| p.toLinearMap.map_add x y

instance [ContinuousMul R] :
    MulActionSemiHomClass (ContinuousPerfectPairing R M N) (id : R → R) M (N →L[R] R) where
  map_smulₛₗ p r x := ContinuousLinearMap.coe_injective <| p.toLinearMap.map_smul r x

instance [ContinuousAdd R] [ContinuousMul R] :
    SemilinearMapClass (ContinuousPerfectPairing R M N) (.id R) M (N →L[R] R) where

variable (p) in
/-- Given a perfect pairing between `M`and `N`, we may interchange the roles of `M` and `N`. -/
def flip : ContinuousPerfectPairing R N M where
  toLinearMap := p.toLinearMap.flip
  continuous_uncurry := p.continuous_uncurry.comp continuous_swap
  bijective_left' := p.bijective_right'
  bijective_right' := p.bijective_left'

@[simp] lemma flip_apply (y : N) (x : M) : p.flip y x = p x y := rfl

variable (p)

lemma bijective : Bijective p := p.bijective_left'
lemma injective : Injective p := p.bijective.injective
lemma surjective : Surjective p := p.bijective.surjective

end ContinuousPerfectPairing
