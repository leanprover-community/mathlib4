/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Symmetrization

If a finite group `G` acts on a commutative additive monoid `M`, the symmetrization of
an element `m : M` by the `G`-action is the sum of `g • m` over all `g : G`.
`symmetrize G M` is defined to be the symmetrization operation as an additive monoid homomorphism.
Notice that we do not include normalization by a `1/#G` factor, which requires stronger assumptions.
If the action is distributive, `symmetrize G M m` is invariant under the `G`-action.

See also `MulAction.automorphize`.

TODO: If useful, we could add versions where `G` is additive and/or `M` is multiplicative.

-/

open scoped BigOperators

variable (G R M : Type*) [Group G] [Fintype G] [Semiring R]
  [AddCommMonoid M] [DistribMulAction G M] [Module R M] [SMulCommClass G R M]

namespace AddMonoidHom

/-- Symmetrization by a group action as an additive monoid homomorphism. -/
@[simps] def symmetrize : M →+ M where
  toFun m := ∑ g : G, g • m
  map_zero' := by simp_rw [smul_zero, Finset.sum_const, nsmul_zero]
  map_add' _ _ := by simp_rw [smul_add, Finset.sum_add_distrib]

variable (g : G) (m : M) {G M}

/-- Symmetrization produces an element invariant under the action. -/
theorem smul_symmetrize : g • symmetrize G M m = symmetrize G M m := by
  simp_rw [symmetrize_apply, Finset.smul_sum, smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ ↦ rfl

theorem stabilizer_symmetrize : MulAction.stabilizer G (symmetrize G M m) = ⊤ :=
  top_unique fun g _ ↦ smul_symmetrize g m

end AddMonoidHom

namespace LinearMap

/-- Symmetrization by a group action as a linear map. -/
def symmetrize : M →ₗ[R] M where
  __ := AddMonoidHom.symmetrize G M
  map_smul' _ _ := by simp_rw [AddMonoidHom.symmetrize, smul_comm, Finset.smul_sum]; rfl

variable {G M} (g : G) (m : M)

theorem symmetrize_apply : symmetrize G R M m = ∑ g : G, g • m := AddMonoidHom.symmetrize_apply ..

/-- Symmetrization produces an element invariant under the action. -/
theorem smul_symmetrize : g • symmetrize G R M m = symmetrize G R M m :=
  AddMonoidHom.smul_symmetrize g m

theorem stabilizer_symmetrize : MulAction.stabilizer G (symmetrize G R M m) = ⊤ :=
  AddMonoidHom.stabilizer_symmetrize m

end LinearMap

namespace ContinuousLinearMap

variable [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul G M]

/-- Symmetrization by a group action as a linear map. -/
def symmetrize : M →L[R] M where
  __ := LinearMap.symmetrize G R M
  cont := by
    exact continuous_finset_sum _ fun g _ ↦ continuous_const_smul g

variable {G M} (g : G) (m : M)

theorem symmetrize_apply : symmetrize G R M m = ∑ g : G, g • m := rfl

/-- Symmetrization produces an element invariant under the action. -/
theorem smul_symmetrize : g • symmetrize G R M m = symmetrize G R M m :=
  AddMonoidHom.smul_symmetrize g m

theorem stabilizer_symmetrize : MulAction.stabilizer G (symmetrize G R M m) = ⊤ :=
  AddMonoidHom.stabilizer_symmetrize m

end ContinuousLinearMap
