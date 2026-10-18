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

The reusable ingredients are `Algebra.FormallyUnramified.smulIdempotent`,
`Algebra.FormallyUnramified.linearize`, and `Algebra.FormallyUnramified.subgroupIdempotent`.
The subgroup idempotent only requires the subgroup to be finite; the coset sum does not require
normality of the subgroup.

Linearizing the coset sum after multiplication by the subgroup idempotent gives multiplication
by `Algebra.FormallyUnramified.descentMultiplier`.
-/

@[expose] public section

open scoped Pointwise TensorProduct

namespace Algebra.FormallyUnramified

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [FormallyUnramified A B] [EssFiniteType A B]

lemma isIdempotentElem_elem : IsIdempotentElem (elem A B) := by
  suffices ∀ t, t * elem A B = TensorProduct.lmul' A t ⊗ₜ[A] 1 * elem A B by
    simpa [IsIdempotentElem, lmul_elem, ← Algebra.TensorProduct.one_def] using this (elem A B)
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b => rw [TensorProduct.lmul'_apply_tmul, ← one_mul 1, ← TensorProduct.tmul_mul_tmul,
      mul_assoc, ← one_tmul_mul_elem, ← mul_assoc, TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add t₁ t₂ h₁ h₂ => rw [map_add, TensorProduct.add_tmul, add_mul, add_mul, h₁, h₂]

open Algebra.TensorProduct

variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The separability tensor evaluated at the identity and the action of `g`. Modulo an ideal
`Q`, it equals `1` exactly when `g` belongs to `Q.inertia G`. -/
noncomputable def smulIdempotent (g : G) : B :=
  productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B g) (elem A B)

lemma isIdempotentElem_smulIdempotent (g : G) : IsIdempotentElem (smulIdempotent A B g) :=
  (isIdempotentElem_elem A B).map (productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B g))

lemma smulIdempotent_mul_smul (g : G) (b : B) :
    smulIdempotent A B g * (g • b) = smulIdempotent A B g * b := by
  simpa [smulIdempotent, mul_comm] using
    congr(productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B g) $(one_tmul_mul_elem b))

@[simp]
lemma smulIdempotent_one : smulIdempotent A B (1 : G) = 1 := by
  have h : productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B (1 : G)) = lmul' A := by
    ext <;> simp
  simpa [smulIdempotent, h] using lmul_elem

@[simp]
lemma mk_smulIdempotent_eq_one_iff (Q : Ideal B) (g : G) :
    Ideal.Quotient.mk Q (smulIdempotent A B g) = 1 ↔ g ∈ Q.inertia G := by
  simp_rw [Q.mem_inertia, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  refine ⟨fun he b ↦ ?_, fun hg ↦ ?_⟩
  · simpa [he] using congr(Ideal.Quotient.mk Q $(smulIdempotent_mul_smul A B g b))
  · rw [← map_one (Ideal.Quotient.mk Q), ← smulIdempotent_one A B (G := G)]
    simp_rw [smulIdempotent, ← Ideal.Quotient.mkₐ_eq_mk A, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp [hg]

open Classical in
lemma mk_smulIdempotent (Q : Ideal B) [Q.IsPrime] (g : G) :
    Ideal.Quotient.mk Q (smulIdempotent A B g) = if g ∈ Q.inertia G then 1 else 0 := by
  have h := IsIdempotentElem.iff_eq_zero_or_one.mp
    ((isIdempotentElem_smulIdempotent A B g).map (Ideal.Quotient.mk Q))
  grind [mk_smulIdempotent_eq_one_iff]

variable {A B}

section Linearize

variable {L M N : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module A M] [Module B M] [IsScalarTower A B M]
  [Module A N] [Module B N] [IsScalarTower A B N]
  [Module A L] [Module B L] [IsScalarTower A B L]

variable (B) in
/-- Separability turns a base-linear map into an algebra-linear map. -/
noncomputable def linearize : (M →ₗ[A] N) →ₗ[B] (M →ₗ[B] N) :=
  ((sec A B M).lcomp B N).comp (LinearMap.liftBaseChangeEquiv B).toLinearMap

lemma linearize_apply (f : M →ₗ[A] N) : linearize B f = (f.liftBaseChange B).comp (sec A B M) :=
  rfl

lemma le_comap_linearize (f : M →ₗ[A] N) (P : Submodule B M) (Q : Submodule B N)
    (hf : P.restrictScalars A ≤ (Q.restrictScalars A).comap f) : P ≤ Q.comap (linearize B f) := by
  intro x hx
  simp_rw [Submodule.mem_comap, linearize_apply, sec, LinearMap.comp_apply, LinearMap.coe_mk]
  induction elem A B using TensorProduct.inductionOn with
  | tmul a b => exact Q.smul_mem a (hf (P.smul_mem b hx))
  | add t₁ t₂ h₁ h₂ => simpa using Q.add_mem h₁ h₂

@[simp]
lemma linearize_comp (f : M →ₗ[A] N) (g : L →ₗ[B] M) :
    linearize B (f.comp (g.restrictScalars A)) = (linearize B f).comp g := by
  ext x
  simp_rw [linearize_apply, sec, LinearMap.comp_apply, LinearMap.coe_mk]
  induction elem A B using TensorProduct.inductionOn with
  | tmul => simp
  | add => simp_all

@[simp]
lemma linearize_comp_mulLeft (f : B →ₗ[A] N) (b : B) :
    linearize B (f.comp (LinearMap.mulLeft A b)) = (linearize B f).comp (LinearMap.mulLeft B b) :=
  linearize_comp f (LinearMap.mulLeft B b)

@[simp]
lemma comp_linearize (g : N →ₗ[B] L) (f : M →ₗ[A] N) :
    linearize B ((g.restrictScalars A).comp f) = g.comp (linearize B f) := by
  rw [linearize_apply, linearize_apply, ← LinearMap.comp_assoc, LinearMap.liftBaseChange_comp]

@[simp]
lemma linearize_id : linearize B (LinearMap.id : M →ₗ[A] M) = LinearMap.id :=
  comp_sec A B M

@[simp]
lemma linearize_restrictScalars (f : M →ₗ[B] N) : linearize B (f.restrictScalars A) = f := by
  simpa using comp_linearize f (LinearMap.id (R := A))

@[simp]
lemma linearize_toAlgHom (g : G) :
    linearize B (MulSemiringAction.toAlgHom A B g).toLinearMap =
      LinearMap.mulLeft B (smulIdempotent A B g) := by
  apply LinearMap.ext_ring
  simp_rw [linearize_apply, sec, LinearMap.comp_apply, LinearMap.coe_mk, smulIdempotent]
  induction elem A B using TensorProduct.inductionOn with
  | tmul => simp
  | add => simp_all

end Linearize

variable (A B) (H : Subgroup G) [Finite H]

/-- The idempotent whose multiples are fixed by a finite subgroup. -/
noncomputable def subgroupIdempotent : B :=
  letI := Fintype.ofFinite H
  ∏ h : H, smulIdempotent A B (h : G)

lemma isIdempotentElem_subgroupIdempotent : IsIdempotentElem (subgroupIdempotent A B H) := by
  classical
  let := Fintype.ofFinite H
  rw [IsIdempotentElem, subgroupIdempotent, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ ↦ (isIdempotentElem_smulIdempotent A B (h : G)).eq

lemma subgroupIdempotent_mul_smul (h : H) (b : B) :
    subgroupIdempotent A B H * (h • b) = subgroupIdempotent A B H * b := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨w, hw⟩ : smulIdempotent A B (h : G) ∣ subgroupIdempotent A B H :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  rw [Subgroup.smul_def, hw, mul_right_comm, smulIdempotent_mul_smul, mul_right_comm]

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

omit [Finite H] in
/-- The multiplier obtained by linearizing the coset sum after multiplication by the subgroup
idempotent. -/
noncomputable def descentMultiplier [Finite G] : B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, smulIdempotent A B q.out * subgroupIdempotent A B H

private lemma descentMultiplier_mem_colon [Algebra.IsInvariant A B G]
    [Finite G] (I : Ideal B) (hI : ∀ g : G, g • I = I) :
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
    Finset.sum_mul, mul_assoc] using le_comap_linearize T I J hT

lemma mk_descentMultiplier_inertia (Q : Ideal B) [Q.IsPrime] [Finite G] :
    Ideal.Quotient.mk Q (descentMultiplier A B (Q.inertia G)) = 1 := by
  classical
  simpa [descentMultiplier, mk_smulIdempotent, ite_mul,
    ← SetLike.mem_coe, ← QuotientGroup.preimage_mk_one] using
      (mk_subgroupIdempotent_inertia_eq_one A B Q)

theorem map_comap_eq_of_isInvariant [Finite G] [Algebra.IsInvariant A B G]
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
