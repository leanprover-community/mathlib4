/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
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
`Algebra.FormallyUnramified.linearize`, `Subgroup.relativeTrace`, and
`Subgroup.inertiaIdempotent`. Relative trace is unnormalized and does not require normality
of the subgroup; the inertia idempotent only requires that subgroup to be finite.

The identity `Subgroup.linearize_descentTrace` explains the multiplier: linearizing
`Subgroup.descentTrace` gives multiplication by `Subgroup.descentMultiplier`.
-/

@[expose] public section

namespace Subgroup

section RelativeTrace

variable {G M : Type*} [Group G] [AddCommMonoid M] [DistribMulAction G M]
  (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The unnormalized relative trace from subgroup-fixed points to group-fixed points. -/
noncomputable def relativeTrace : FixedPoints.addSubmonoid H M →+ FixedPoints.addSubmonoid G M where
  toFun x := ⟨∑ q : G ⧸ H, q.out • x, fun g ↦ by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q ↦ ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
    rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out] at hh
    change g • (q.out • (x : M)) = (g • q).out • (x : M)
    simp only [hh, smul_eq_mul, mul_smul, show (h : G) • (x : M) = x from x.property h]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [smul_add, Finset.sum_add_distrib])

lemma relativeTrace_apply (x : FixedPoints.addSubmonoid H M) :
    (H.relativeTrace x : M) = ∑ q : G ⧸ H, q.out • (x : M) := rfl

lemma relativeTrace_mem (P : AddSubmonoid M)
    (hP : ∀ (g : G) x, x ∈ P → g • x ∈ P)
    (x : FixedPoints.addSubmonoid H M) (hx : (x : M) ∈ P) :
    (H.relativeTrace x : M) ∈ P :=
  P.sum_mem fun q _ ↦ hP q.out _ hx

noncomputable def relativeTraceLinearMap {A B : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] :
    FixedPoints.subalgebra A B H →ₗ[A] FixedPoints.subalgebra A B G where
  __ := H.relativeTrace (M := B)
  map_smul' a x := Subtype.ext <|
    (Finset.sum_congr rfl fun q _ ↦ smul_comm q.out a (x : B)).trans Finset.smul_sum.symm

lemma relativeTraceLinearMap_apply {A B : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
    (x : FixedPoints.subalgebra A B H) :
    (H.relativeTraceLinearMap (A := A) (B := B) x : B) = ∑ q : G ⧸ H, q.out • (x : B) := rfl

end RelativeTrace

end Subgroup

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

end Algebra.FormallyUnramified

namespace Algebra.FormallyUnramified

open Algebra.TensorProduct

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [FormallyUnramified A B] [EssFiniteType A B]

/-- The separability tensor evaluated at two algebra maps. Its support is their equalizer. -/
noncomputable def equalizerIdempotent (f g : B →ₐ[A] C) : C :=
  productMap f g (elem A B)

lemma isIdempotentElem_equalizerIdempotent (f g : B →ₐ[A] C) :
    IsIdempotentElem (equalizerIdempotent f g) :=
  (isIdempotentElem_elem A B).map (productMap f g)

lemma mul_equalizerIdempotent (f g : B →ₐ[A] C) (b : B) :
    g b * equalizerIdempotent f g = f b * equalizerIdempotent f g := by
  simpa [equalizerIdempotent] using congr(productMap f g $(one_tmul_mul_elem b))

lemma equalizerIdempotent_mul (f g : B →ₐ[A] C) (b : B) :
    equalizerIdempotent f g * f b = equalizerIdempotent f g * g b := by
  grind [mul_equalizerIdempotent f g b]

@[simp]
lemma equalizerIdempotent_self (f : B →ₐ[A] C) : equalizerIdempotent f f = 1 := by
  have h : productMap f f = f.comp (lmul' A) := by ext <;> simp
  simp [equalizerIdempotent, h, lmul_elem]

@[simp]
lemma equalizerIdempotent_eq_one_iff (f g : B →ₐ[A] C) :
    equalizerIdempotent f g = 1 ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [AlgHom.ext_iff, h] using equalizerIdempotent_mul f g
  · simp [h]

lemma map_equalizerIdempotent {D : Type*} [CommRing D] [Algebra A D]
    (f g : B →ₐ[A] C) (k : C →ₐ[A] D) :
    k (equalizerIdempotent f g) = equalizerIdempotent (k.comp f) (k.comp g) := by
  have h : k.comp (productMap f g) = productMap (k.comp f) (k.comp g) := by ext <;> simp
  exact congr($h (elem A B))

lemma mk_equalizerIdempotent_eq_one_iff (f g : B →ₐ[A] C) (Q : Ideal C) :
    Ideal.Quotient.mk Q (equalizerIdempotent f g) = 1 ↔
      (Ideal.Quotient.mkₐ A Q).comp f = (Ideal.Quotient.mkₐ A Q).comp g := by
  rw [← Ideal.Quotient.mkₐ_eq_mk A Q, map_equalizerIdempotent, equalizerIdempotent_eq_one_iff]

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

lemma le_comap_lineraize (f : M →ₗ[A] N) (P : Submodule B M) (Q : Submodule B N)
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
lemma linearize_toLinearMap (f : B →ₐ[A] B) :
    linearize B f.toLinearMap = LinearMap.mulLeft B (equalizerIdempotent (AlgHom.id A B) f) := by
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
  ∏ h : H, equalizerIdempotent (AlgHom.id A B) (MulSemiringAction.toAlgHom A B h)

lemma isIdempotentElem_inertiaIdempotent : IsIdempotentElem (H.inertiaIdempotent A B) := by
  classical
  let := Fintype.ofFinite H -- missing IsIdempotentElem.prod?
  rw [IsIdempotentElem, inertiaIdempotent, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ ↦ (isIdempotentElem_equalizerIdempotent _ _).eq

lemma inertiaIdempotent_mul_smul (h : H) (b : B) :
    H.inertiaIdempotent A B * (h • b) = H.inertiaIdempotent A B * b := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨w, hw⟩ : equalizerIdempotent (AlgHom.id A B)
      (MulSemiringAction.toAlgHom A B h) ∣ H.inertiaIdempotent A B :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  have he := equalizerIdempotent_mul (AlgHom.id A B) (MulSemiringAction.toAlgHom A B h) b
  rw [AlgHom.id_apply, MulSemiringAction.toAlgHom_apply] at he
  rw [hw, mul_right_comm, ← he, mul_right_comm]

@[simp]
lemma smul_inertiaIdempotent (h : H) :
    h • H.inertiaIdempotent A B = H.inertiaIdempotent A B := by
  have h₁ := (H.inertiaIdempotent_mul_smul A B h (H.inertiaIdempotent A B)).trans
    (H.isIdempotentElem_inertiaIdempotent A B).eq
  have h₂ : (h • H.inertiaIdempotent A B) * H.inertiaIdempotent A B =
      h • (H.inertiaIdempotent A B) := by
    simpa only [smul_mul', smul_smul, mul_inv_cancel, one_smul] using
      congrArg (h • ·) ((H.inertiaIdempotent_mul_smul A B h⁻¹ (H.inertiaIdempotent A B)).trans
        (H.isIdempotentElem_inertiaIdempotent A B).eq)
  exact h₂.symm.trans ((mul_comm _ _).trans h₁)

lemma smul_inertiaIdempotent_mul (h : H) (b : B) :
    h • (H.inertiaIdempotent A B * b) = H.inertiaIdempotent A B * b := by
  rw [smul_mul', smul_inertiaIdempotent, inertiaIdempotent_mul_smul]

variable {H A B} in
lemma inertiaIdempotent_sub_one_mem_iff {Q : Ideal B} :
    Ideal.Quotient.mk Q (H.inertiaIdempotent A B) = 1 ↔ H ≤ Q.inertia G := by
  refine ⟨fun hu h hh ↦ Q.mem_inertia.mpr fun b ↦ ?_, fun hH ↦ ?_⟩
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [hu] using congrArg (Ideal.Quotient.mk Q) (H.inertiaIdempotent_mul_smul A B ⟨h, hh⟩ b)
  · rw [inertiaIdempotent, map_prod]
    apply Finset.prod_eq_one
    intro h hh
    rw [mk_equalizerIdempotent_eq_one_iff, eq_comm]
    ext b
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Subgroup.smul_def] using Q.mem_inertia.mp (hH h.2) b

lemma _root_.Ideal.mk_inertiaIdempotent_inertia_eq_one (Q : Ideal B) [Finite (Q.inertia G)] :
    Ideal.Quotient.mk Q ((Q.inertia G).inertiaIdempotent A B) = 1 :=
  inertiaIdempotent_sub_one_mem_iff.mpr le_rfl

open Classical in
lemma _root_.Ideal.Quotient.mk_equalizerIdempotent (Q : Ideal B) [Q.IsPrime] (g : G) :
    Ideal.Quotient.mk Q (equalizerIdempotent (AlgHom.id A B)
      (MulSemiringAction.toAlgHom A B g)) = if g ∈ Q.inertia G then 1 else 0 := by
  have h {u : B ⧸ Q} (hu : IsIdempotentElem u) : u = if u = 1 then 1 else 0 := by
    grind [IsIdempotentElem.iff_eq_zero_or_one]
  rw [h ((isIdempotentElem_equalizerIdempotent (AlgHom.id A B)
    (MulSemiringAction.toAlgHom A B g)).map (Ideal.Quotient.mk Q))]
  simp [mk_equalizerIdempotent_eq_one_iff, AlgHom.ext_iff,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Q.toAddSubgroup.sub_mem_comm_iff]

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
  exact ∑ q : G ⧸ H, equalizerIdempotent (AlgHom.id A B)
    (MulSemiringAction.toAlgHom A B q.out) * H.inertiaIdempotent A B

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
    let y : FixedPoints.addSubmonoid H B :=
      ⟨H.inertiaIdempotent A B * x, fun h ↦ H.smul_inertiaIdempotent_mul A B h x⟩
    have hy : (H.relativeTrace y : B) ∈ I := H.relativeTrace_mem I.toAddSubmonoid
      (fun g x hx ↦ hI g ▸ Ideal.smul_mem_pointwise_smul g x I hx) y (I.mul_mem_left _ hx)
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) _ (H.relativeTrace y).property
    have : algebraMap A B a ∈ J := Ideal.mem_map_of_mem _ (by simpa [ha] using hy)
    simpa [Subgroup.descentTrace, Subgroup.relativeTrace_apply, y, ha] using this
  simpa [Submodule.mem_colon, IsConcreteLE.le_iff, Subgroup.linearize_descentTrace] using
    le_comap_lineraize (H.descentTrace A B) I J hT

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
