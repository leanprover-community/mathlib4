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

The reusable ingredients are `Algebra.FormallyUnramified.equalizerIdempotent`,
`Algebra.FormallyUnramified.linearize`, and `Subgroup.inertiaIdempotent`.
The inertia idempotent only requires the subgroup to be finite; the coset sum does not require
normality of the subgroup.

The identity `Subgroup.linearize_descentTrace` explains the multiplier: linearizing
`Subgroup.descentTrace` gives multiplication by `Subgroup.descentMultiplier`.
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
noncomputable def equalizerIdempotent (g : G) : B :=
  productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B g) (elem A B)

lemma isIdempotentElem_equalizerIdempotent (g : G) :
    IsIdempotentElem (equalizerIdempotent A B g) :=
  (isIdempotentElem_elem A B).map (productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B g))

lemma equalizerIdempotent_mul_smul (g : G) (b : B) :
    equalizerIdempotent A B g * (g • b) = equalizerIdempotent A B g * b := by
  simpa [equalizerIdempotent, mul_comm] using
    congr(productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B g) $(one_tmul_mul_elem b))

@[simp]
lemma equalizerIdempotent_one : equalizerIdempotent A B (1 : G) = 1 := by
  have h : productMap (AlgHom.id A B) (MulSemiringAction.toAlgHom A B (1 : G)) = lmul' A := by
    ext <;> simp
  simpa [equalizerIdempotent, h] using lmul_elem (R := A) (S := B)

@[simp]
lemma _root_.Ideal.Quotient.mk_equalizerIdempotent_eq_one_iff (Q : Ideal B) (g : G) :
    Ideal.Quotient.mk Q (equalizerIdempotent A B g) = 1 ↔ g ∈ Q.inertia G := by
  refine ⟨fun he ↦ Q.mem_inertia.mpr fun b ↦ ?_, fun hg ↦ ?_⟩
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [he] using congrArg (Ideal.Quotient.mk Q) (equalizerIdempotent_mul_smul A B g b)
  · rw [← map_one (Ideal.Quotient.mk Q), ← equalizerIdempotent_one A B (G := G)]
    simp only [equalizerIdempotent, ← Ideal.Quotient.mkₐ_eq_mk A, ← AlgHom.comp_apply]
    congr 1
    ext b <;> simp [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Q.mem_inertia.mp hg]

open Classical in
lemma _root_.Ideal.Quotient.mk_equalizerIdempotent (Q : Ideal B) [Q.IsPrime] (g : G) :
    Ideal.Quotient.mk Q (equalizerIdempotent A B g) = if g ∈ Q.inertia G then 1 else 0 := by
  have h := IsIdempotentElem.iff_eq_zero_or_one.mp
    ((isIdempotentElem_equalizerIdempotent A B g).map (Ideal.Quotient.mk Q))
  by_cases hg : g ∈ Q.inertia G <;> simp_all

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
      LinearMap.mulLeft B (equalizerIdempotent A B g) := by
  apply LinearMap.ext_ring
  simp_rw [linearize_apply, sec, LinearMap.comp_apply, LinearMap.coe_mk, equalizerIdempotent]
  induction elem A B using TensorProduct.inductionOn with
  | tmul => simp
  | add => simp_all

end Linearize

end Algebra.FormallyUnramified

open Algebra.FormallyUnramified

variable {G : Type*} [Group G] (H : Subgroup G) (A : Type*) (B : Type*)
  [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] [Finite H]

namespace Subgroup

/-- The idempotent whose multiples are fixed by a finite subgroup. -/
noncomputable def inertiaIdempotent : B :=
  letI := Fintype.ofFinite H
  ∏ h : H, equalizerIdempotent A B (h : G)

lemma isIdempotentElem_inertiaIdempotent : IsIdempotentElem (H.inertiaIdempotent A B) := by
  classical
  let := Fintype.ofFinite H
  rw [IsIdempotentElem, inertiaIdempotent, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ ↦ (isIdempotentElem_equalizerIdempotent A B (h : G)).eq

lemma inertiaIdempotent_mul_smul (h : H) (b : B) :
    H.inertiaIdempotent A B * (h • b) = H.inertiaIdempotent A B * b := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨w, hw⟩ : equalizerIdempotent A B (h : G) ∣ H.inertiaIdempotent A B :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  rw [Subgroup.smul_def, hw, mul_right_comm, equalizerIdempotent_mul_smul, mul_right_comm]

@[simp]
lemma smul_inertiaIdempotent (h : H) :
    h • H.inertiaIdempotent A B = H.inertiaIdempotent A B := by
  calc
    h • H.inertiaIdempotent A B =
        h • (H.inertiaIdempotent A B * (h⁻¹ • H.inertiaIdempotent A B)) := by
      rw [inertiaIdempotent_mul_smul, (H.isIdempotentElem_inertiaIdempotent A B).eq]
    _ = H.inertiaIdempotent A B := by
      rw [smul_mul', smul_inv_smul, mul_comm, inertiaIdempotent_mul_smul,
        (H.isIdempotentElem_inertiaIdempotent A B).eq]

lemma smul_inertiaIdempotent_mul (h : H) (b : B) :
    h • (H.inertiaIdempotent A B * b) = H.inertiaIdempotent A B * b := by
  rw [smul_mul', smul_inertiaIdempotent, inertiaIdempotent_mul_smul]

variable {H A B} in
lemma mk_inertiaIdempotent_eq_one_iff {Q : Ideal B} :
    Ideal.Quotient.mk Q (H.inertiaIdempotent A B) = 1 ↔ H ≤ Q.inertia G := by
  refine ⟨fun hu h hh ↦ Q.mem_inertia.mpr fun b ↦ ?_, fun hH ↦ ?_⟩
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [hu] using congrArg (Ideal.Quotient.mk Q) (H.inertiaIdempotent_mul_smul A B ⟨h, hh⟩ b)
  · rw [inertiaIdempotent, map_prod]
    exact Finset.prod_eq_one fun h _ ↦ by simpa using hH h.2

lemma _root_.Ideal.mk_inertiaIdempotent_inertia_eq_one (Q : Ideal B) [Finite (Q.inertia G)] :
    Ideal.Quotient.mk Q ((Q.inertia G).inertiaIdempotent A B) = 1 :=
  mk_inertiaIdempotent_eq_one_iff.mpr le_rfl

omit [Finite H] in
/-- Relative trace after multiplication by the inertia idempotent, viewed as a base-linear
endomorphism. Its linearization is multiplication by `descentMultiplier`. -/
noncomputable def descentTrace [Finite G] : B →ₗ[A] B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact (∑ q : G ⧸ H, (MulSemiringAction.toAlgHom A B q.out).toLinearMap).comp
    (LinearMap.mulLeft A (H.inertiaIdempotent A B))

omit [Finite H] in
/-- The multiplier representing the linearization of `descentTrace`. -/
noncomputable def descentMultiplier [Finite G] : B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, equalizerIdempotent A B q.out * H.inertiaIdempotent A B

/-- Linearizing the relative trace after multiplication by the inertia idempotent gives
multiplication by the descent multiplier. -/
@[simp]
lemma linearize_descentTrace [Finite G] :
    linearize B (H.descentTrace A B) = LinearMap.mulLeft B (H.descentMultiplier A B) := by
  classical
  apply LinearMap.ext_ring
  simp [descentMultiplier, descentTrace]

end Subgroup

namespace Ideal

private lemma descentMultiplier_mem_colon [Algebra.IsInvariant A B G]
    [Finite G] (I : Ideal B) (hI : ∀ g : G, g • I = I) :
      H.descentMultiplier A B ∈ ((I.comap (algebraMap A B)).map (algebraMap A B)).colon I := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  set J := (I.comap (algebraMap A B)).map (algebraMap A B)
  have hT : I.restrictScalars A ≤ (J.restrictScalars A).comap (H.descentTrace A B) := by
    intro x hx
    let y := H.inertiaIdempotent A B * x
    have hy (g : G) : g • (∑ q : G ⧸ H, q.out • y) = ∑ q : G ⧸ H, q.out • y := by
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q ↦ ?_
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
      rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out] at hh
      change g • (q.out • y) = (g • q).out • y
      simp only [hh, smul_eq_mul, mul_smul,
        show (h : G) • y = y from H.smul_inertiaIdempotent_mul A B h x]
    have hyI : (∑ q : G ⧸ H, q.out • y) ∈ I := I.sum_mem fun q _ ↦
      hI q.out ▸ Ideal.smul_mem_pointwise_smul q.out y I (I.mul_mem_left _ hx)
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) _ hy
    have : algebraMap A B a ∈ J := Ideal.mem_map_of_mem _ (by simpa [ha] using hyI)
    simpa [Subgroup.descentTrace, y, ha] using this
  simpa [Submodule.mem_colon, IsConcreteLE.le_iff, Subgroup.linearize_descentTrace] using
    le_comap_linearize (H.descentTrace A B) I J hT

lemma Quotient.mk_descentMultiplier_inertia (Q : Ideal B) [Q.IsPrime] [Finite G] :
    Quotient.mk Q ((Q.inertia G).descentMultiplier A B) = 1 := by
  classical
  simpa [Subgroup.descentMultiplier, Quotient.mk_equalizerIdempotent, ite_mul,
    ← SetLike.mem_coe, ← QuotientGroup.preimage_mk_one] using
      (Q.mk_inertiaIdempotent_inertia_eq_one A)

theorem map_comap_eq_of_isInvariant_of_unramified [Finite G] [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  classical
  set J := (I.comap (algebraMap A B)).map (algebraMap A B)
  apply le_antisymm Ideal.map_comap_le
  suffices J.colon (I : Set B) = ⊤ from (Submodule.colon_eq_top_iff_subset _).mp this
  by_contra hJ
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal (J.colon (I : Set B)) hJ
  let : m.IsMaximal := hm
  have := Quotient.eq_zero_iff_mem.mpr (hKm (descentMultiplier_mem_colon (m.inertia G) A B I hI))
  rw [Quotient.mk_descentMultiplier_inertia A] at this
  exact one_ne_zero this

end Ideal
