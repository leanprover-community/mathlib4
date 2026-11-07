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

namespace LinearMap

variable {R M N : Type*} (A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]

variable {A} in
lemma Submodule.baseChange_le_comap_liftBaseChange_iff
    {l : M →ₗ[R] N} {p : Submodule R M} {q : Submodule A N} :
    p.baseChange A ≤ q.comap (l.liftBaseChange A) ↔ p ≤ (q.restrictScalars R).comap l := by
  -- seems like we're missing some API lemma for `LinearMap.liftBaseChangeEquiv_symm`
  have h : (l.liftBaseChange A).restrictScalars R ∘ₗ TensorProduct.mk R A M 1 = l :=
    (LinearMap.liftBaseChangeEquiv A).symm_apply_apply l
  rw [Submodule.baseChange_le_iff_le_comap, Submodule.restrictScalars_comap,
    ← Submodule.comap_comp, h]

end LinearMap

end LiftBaseChange

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

section finite

variable [Finite H]

/-- The idempotent whose multiples are fixed by a finite subgroup. -/
noncomputable def subgroupIdempotent : B :=
  letI := Fintype.ofFinite H
  ∏ h : H, inertiaIdempotent A B (h : G)

lemma isIdempotentElem_subgroupIdempotent : IsIdempotentElem (subgroupIdempotent A B H) := by
  classical
  let := Fintype.ofFinite H
  rw [IsIdempotentElem, subgroupIdempotent, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ ↦ (isIdempotentElem_inertiaIdempotent A B (h : G)).eq

lemma subgroupIdempotent_mul_smul (h : H) (b : B) :
    subgroupIdempotent A B H * (h • b) = subgroupIdempotent A B H * b := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨w, hw⟩ : inertiaIdempotent A B (h : G) ∣ subgroupIdempotent A B H :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  rw [Subgroup.smul_def, hw, mul_right_comm, mul_comm _ ((h : G) • b),
    smul_mul_inertiaIdempotent, mul_right_comm]
  grind

@[simp]
lemma smul_subgroupIdempotent (h : H) :
    h • subgroupIdempotent A B H = subgroupIdempotent A B H := by
  calc
    h • subgroupIdempotent A B H =
        h • (subgroupIdempotent A B H * (h⁻¹ • subgroupIdempotent A B H)) := by
      rw [subgroupIdempotent_mul_smul, (isIdempotentElem_subgroupIdempotent A B H).eq]
    _ = subgroupIdempotent A B H := by
      rw [smul_mul', smul_inv_smul, mul_comm, subgroupIdempotent_mul_smul,
        (isIdempotentElem_subgroupIdempotent A B H).eq]

lemma smul_subgroupIdempotent_mul (h : H) (b : B) :
    h • (subgroupIdempotent A B H * b) = subgroupIdempotent A B H * b := by
  rw [smul_mul', smul_subgroupIdempotent, subgroupIdempotent_mul_smul]

variable {H A B} in
lemma mk_subgroupIdempotent_eq_one_iff {Q : Ideal B} :
    Ideal.Quotient.mk Q (subgroupIdempotent A B H) = 1 ↔ H ≤ Q.inertia G := by
  refine ⟨fun hu h hh ↦ Q.mem_inertia.mpr fun b ↦ ?_, fun hH ↦ ?_⟩
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [hu] using congrArg (Ideal.Quotient.mk Q) (subgroupIdempotent_mul_smul A B H ⟨h, hh⟩ b)
  · rw [subgroupIdempotent, map_prod]
    exact Finset.prod_eq_one fun h _ ↦ by simpa using hH h.2

lemma mk_subgroupIdempotent_inertia_eq_one (Q : Ideal B) [Finite (Q.inertia G)] :
    Ideal.Quotient.mk Q (subgroupIdempotent A B (Q.inertia G)) = 1 :=
  mk_subgroupIdempotent_eq_one_iff.mpr le_rfl

end finite

variable [Finite G]

/-- The multiplier obtained by linearizing the coset sum after multiplication by the subgroup
idempotent. -/
noncomputable def descentMultiplier : B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, inertiaIdempotent A B q.out * subgroupIdempotent A B H

private lemma descentMultiplier_mem_colon [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    descentMultiplier A B H ∈ ((I.comap (algebraMap A B)).map (algebraMap A B)).colon I := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let J := (I.comap (algebraMap A B)).map (algebraMap A B)
  let T : B →ₗ[A] B := (∑ q : G ⧸ H, (MulSemiringAction.toAlgHom A B q.out).toLinearMap).comp
    (LinearMap.mulLeft A (subgroupIdempotent A B H))
  have hT : I.restrictScalars A ≤ (J.restrictScalars A).comap T := by
    intro x hx
    let y := subgroupIdempotent A B H * x
    let z := ∑ q : G ⧸ H, q.out • y
    have hz (g : G) : g • z = z := by
      simp only [z, Finset.smul_sum]
      refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q ↦ ?_
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
      rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out] at hh
      have hy : (h : G) • y = y := smul_subgroupIdempotent_mul A B H h x
      simp [hh, mul_smul, hy]
    have hzI : z ∈ I := I.sum_mem fun q _ ↦
      hI q.out ▸ Ideal.smul_mem_pointwise_smul q.out y I (I.mul_mem_left _ hx)
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) z hz
    have : algebraMap A B a ∈ J := Ideal.mem_map_of_mem _ (by simpa [ha] using hzI)
    simpa [T, y, z, ha] using this
  simpa [Submodule.mem_colon, IsConcreteLE.le_iff, descentMultiplier, T,
    Finset.sum_mul, mul_assoc] using le_comap_extendScalars T I J hT

lemma mk_descentMultiplier_inertia (Q : Ideal B) [Q.IsPrime] :
    Ideal.Quotient.mk Q (descentMultiplier A B (Q.inertia G)) = 1 := by
  classical
  simpa [descentMultiplier, mk_inertiaIdempotent, ite_mul,
    ← SetLike.mem_coe, ← QuotientGroup.preimage_mk_one] using
      (mk_subgroupIdempotent_inertia_eq_one A B Q)

theorem map_comap_eq_of_isInvariant [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  classical
  set J := (I.comap (algebraMap A B)).map (algebraMap A B)
  apply le_antisymm Ideal.map_comap_le
  rw [← Submodule.colon_eq_top_iff_le]
  by_contra hJ
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal (J.colon (I : Set B)) hJ
  let : m.IsMaximal := hm
  have := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hKm (descentMultiplier_mem_colon A B (m.inertia G) I hI))
  rw [mk_descentMultiplier_inertia A] at this
  exact one_ne_zero this

end Algebra.FormallyUnramified
