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

namespace Algebra.FormallyUnramified

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S] [FormallyUnramified R S]
  [EssFiniteType R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

@[simp]
lemma sec_one : sec R S S 1 = elem R S := by
  simp [sec_apply, LinearMap.toSpanSingleton_one_eq_algebraLinearMap]

end Algebra.FormallyUnramified

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

-- PRed
@[simp]
lemma extendScalars_eq_mulLeft_inertiaIdempotent (g : G) :
    extendScalars B (MulSemiringAction.toAlgHom A B g).toLinearMap =
      LinearMap.mulLeft B (inertiaIdempotent A B g) := by
  rw [inertiaIdempotent, equalizerIdempotent_comm]
  apply LinearMap.ext_ring
  rw [LinearMap.mulLeft_apply, mul_one, extendScalars_apply,
    LinearMap.coe_comp, Function.comp_apply, sec_one]
  rfl

section extendScalars

variable {L M N : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module A M] [Module B M] [IsScalarTower A B M]
  [Module A N] [Module B N] [IsScalarTower A B N]
  [Module A L] [Module B L] [IsScalarTower A B L]

lemma le_comap_extendScalars (f : M →ₗ[A] N) (P : Submodule B M) (Q : Submodule B N)
    (hf : P.restrictScalars A ≤ (Q.restrictScalars A).comap f) :
    P ≤ Q.comap (extendScalars B f) := by
  suffices h : (P.restrictScalars A).baseChange B ≤ Q.comap (f.liftBaseChange B) from
    fun x hx ↦ h (sec_mem_baseChange A B P hx)
  rw [← (LinearMap.liftBaseChangeEquiv B).symm_apply_apply f] at hf
  rwa [Submodule.baseChange_le_iff_le_comap, Q.restrictScalars_comap, ← Submodule.comap_comp]

end extendScalars

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
