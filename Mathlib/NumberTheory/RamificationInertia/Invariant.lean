/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Unramified.Finite

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.RingTheory.Ideal.Colon

/-!
# Stable ideals in unramified invariant extensions

An ideal stable under a finite group action on an unramified invariant algebra is extended
from the base ring. The proof uses a separability tensor, a multiplier on which the inertia
subgroup acts trivially, and a sum over left cosets of the inertia subgroup.

The reusable ingredients are `Algebra.FormallyUnramified.inertiaIdempotent`,
`Algebra.FormallyUnramified.extendScalars`, and `Algebra.FormallyUnramified.subgroupIdempotent`.
The subgroup idempotent only requires the subgroup to be finite; the coset sum does not require
normality of the subgroup.

Linearizing the coset sum after multiplication by the subgroup idempotent gives multiplication
by `Algebra.FormallyUnramified.descentMultiplier`.
-/

@[expose] public section

open scoped Pointwise TensorProduct

theorem MulAction.smul_sum_quotient_of_fixed {G M : Type*} [Group G] [AddCommMonoid M]
    [DistribMulAction G M] (H : Subgroup G) [Fintype (G ⧸ H)] (x : M)
    (hx : ∀ h : H, h • x = x) (g : G) :
    g • (∑ q : G ⧸ H, q.out • x) = ∑ q : G ⧸ H, q.out • x := by
  classical
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q ↦ ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
  rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out] at hh
  simp [hh, mul_smul, ← Subgroup.smul_def, hx]

namespace Algebra.FormallyUnramified

open Algebra.TensorProduct

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [FormallyUnramified A B] [EssFiniteType A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

variable (A B) (H : Subgroup G)

variable [Finite G]

/-- The multiplier obtained by linearizing the coset sum after multiplication by the subgroup
idempotent. -/
noncomputable def descentMultiplier : B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, inertiaIdempotent A B q.out * groupIdempotent A B H

lemma descentMultiplier_mem_colon [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    descentMultiplier A B H ∈ ((I.under A).map (algebraMap A B)).colon I := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let J := (I.under A).map (algebraMap A B)
  let T : B →ₗ[A] B := ∑ q : G ⧸ H, (MulSemiringAction.toAlgHom A B q.out).toLinearMap.comp
    (LinearMap.mulLeft A (groupIdempotent A B H))
  suffices hT : ∀ x, x ∈ I → T x ∈ J by
    simpa [Submodule.mem_colon, IsConcreteLE.le_iff, descentMultiplier, T,
      Finset.sum_mul, mul_assoc] using le_comap_extendScalars T I J hT
  intro x hx
  let y := x * groupIdempotent A B H
  let z := ∑ q : G ⧸ H, q.out • y
  suffices z ∈ J by simpa [T, mul_comm, -smul_mul']
  have hy (h : H) : h • y = y := by rw [smul_mul', smul_groupIdempotent, smul_mul_groupIdempotent]
  have hz (g : G) : g • z = z := MulAction.smul_sum_quotient_of_fixed H y hy g
  have hyI : y ∈ I := I.mul_mem_right _ hx
  have hzI : z ∈ I := I.sum_mem fun q _ ↦ hI q.out ▸ Ideal.smul_mem_pointwise_smul q.out y I hyI
  exact Algebra.IsInvariant.mem_map_under G hz hzI

lemma mk_descentMultiplier_inertia (Q : Ideal B) [Q.IsPrime] :
    Ideal.Quotient.mk Q (descentMultiplier A B (Q.inertia G)) = 1 := by
  classical
  simp [descentMultiplier, mk_inertiaIdempotent]

theorem map_comap_eq_of_isInvariant [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    (I.under A).map (algebraMap A B) = I := by
  set J := (I.under A).map (algebraMap A B)
  apply le_antisymm Ideal.map_comap_le
  rw [← Submodule.colon_eq_top_iff_le]
  by_contra hJ
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal (J.colon (I : Set B)) hJ
  specialize hKm (descentMultiplier_mem_colon A B (m.inertia G) I hI)
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_descentMultiplier_inertia] at hKm
  exact one_ne_zero hKm

end Algebra.FormallyUnramified
