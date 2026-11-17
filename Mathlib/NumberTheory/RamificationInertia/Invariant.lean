/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Invariant.Defs
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

section LiftBaseChange

lemma Submodule.baseChange_le_comap_liftBaseChange_iff
    {R M N A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]
    {l : M →ₗ[R] N} {p : Submodule R M} {q : Submodule A N} :
    p.baseChange A ≤ q.comap (l.liftBaseChange A) ↔ p ≤ (q.restrictScalars R).comap l := by
  have h : (l.liftBaseChange A).restrictScalars R ∘ₗ TensorProduct.mk R A M 1 = l :=
    (LinearMap.liftBaseChangeEquiv A).symm_apply_apply l
  rw [Submodule.baseChange_le_iff_le_comap, Submodule.restrictScalars_comap, ← Submodule.comap_comp,
    h]

end LiftBaseChange

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

@[to_additive (attr := simp)]
theorem QuotientGroup.mk_eq_one_iff {G : Type*} [Group G] {H : Subgroup G} {g : G} :
    (g : G ⧸ H) = (1 : G) ↔ g ∈ H := by
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage, QuotientGroup.preimage_mk_one, SetLike.mem_coe]

@[to_additive (attr := simp)]
theorem QuotientGroup.out_mem_iff {G : Type*} [Group G] {H : Subgroup G} {g : G ⧸ H} :
    g.out ∈ H ↔ g = (1 : G) := by
  rw [← mk_eq_one_iff, QuotientGroup.out_eq']

namespace Algebra.FormallyUnramified

open Algebra.TensorProduct

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [FormallyUnramified A B] [EssFiniteType A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

section extendScalars

variable {L M N : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module A M] [Module B M] [IsScalarTower A B M]
  [Module A N] [Module B N] [IsScalarTower A B N]
  [Module A L] [Module B L] [IsScalarTower A B L]

lemma le_comap_extendScalars (f : M →ₗ[A] N) (P : Submodule B M) (Q : Submodule B N)
    (hf : P.restrictScalars A ≤ (Q.restrictScalars A).comap f) : P ≤ Q.comap (extendScalars B f) :=
  fun _ hx ↦ Submodule.baseChange_le_comap_liftBaseChange_iff.mpr hf (sec_mem_baseChange A B P hx)

@[simp]
lemma extendScalars_toAlgHom (g : G) :
    extendScalars B (MulSemiringAction.toAlgHom A B g).toLinearMap =
      LinearMap.mulLeft B (inertiaIdempotent A B g) := by
  rw [inertiaIdempotent, equalizerIdempotent_comm]
  apply LinearMap.ext_ring
  rw [LinearMap.mulLeft_apply, mul_one, extendScalars_apply,
    LinearMap.coe_comp, Function.comp_apply, sec_one]
  rfl

end extendScalars

variable (A B) (H : Subgroup G)

variable [Finite G]

/-- The multiplier obtained by linearizing the coset sum after multiplication by the subgroup
idempotent. -/
noncomputable def descentMultiplier : B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, inertiaIdempotent A B q.out * groupIdempotent A B H

private lemma descentMultiplier_mem_colon [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    descentMultiplier A B H ∈ ((I.comap (algebraMap A B)).map (algebraMap A B)).colon I := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let J := (I.comap (algebraMap A B)).map (algebraMap A B)
  let T : B →ₗ[A] B := (∑ q : G ⧸ H, (MulSemiringAction.toAlgHom A B q.out).toLinearMap).comp
    (LinearMap.mulLeft A (groupIdempotent A B H))
  suffices hT : I.restrictScalars A ≤ (J.restrictScalars A).comap T by
    simpa [Submodule.mem_colon, IsConcreteLE.le_iff, descentMultiplier, T,
      Finset.sum_mul, mul_assoc] using le_comap_extendScalars T I J hT
  intro x hx
  let y := x * groupIdempotent A B H
  let z := ∑ q : G ⧸ H, q.out • y
  have hy (h : H) : (h : G) • y = y := by
    simpa only [y, smul_mul', ← Subgroup.smul_def,
      smul_groupIdempotent] using smul_mul_groupIdempotent A h x
  have hz (g : G) : g • z = z := MulAction.smul_sum_quotient_of_fixed H y hy g
  have hzI : z ∈ I := I.sum_mem fun q _ ↦
    hI q.out ▸ Ideal.smul_mem_pointwise_smul q.out y I (I.mul_mem_right _ hx)
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) z hz
  have : algebraMap A B a ∈ J := Ideal.mem_map_of_mem _ (by simpa [ha] using hzI)
  simpa [T, y, z, ha, mul_comm] using this

lemma mk_descentMultiplier_inertia (Q : Ideal B) [Q.IsPrime] :
    Ideal.Quotient.mk Q (descentMultiplier A B (Q.inertia G)) = 1 := by
  classical
  simp [descentMultiplier, mk_inertiaIdempotent]

theorem map_comap_eq_of_isInvariant [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  set J := (I.comap (algebraMap A B)).map (algebraMap A B)
  apply le_antisymm Ideal.map_comap_le
  rw [← Submodule.colon_eq_top_iff_le]
  by_contra hJ
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal (J.colon (I : Set B)) hJ
  specialize hKm (descentMultiplier_mem_colon A B (m.inertia G) I hI)
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_descentMultiplier_inertia] at hKm
  exact one_ne_zero hKm

end Algebra.FormallyUnramified
