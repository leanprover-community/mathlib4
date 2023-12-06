/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Discriminant

/-!
# The different ideal

## Main definition
- `Submodule.traceDual`: The dual `L`-sub `B`-module under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.

## TODO
- Define the relative different ideal
- Show properties of the different ideal
-/

universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A K) {L : Type u} {B} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsDomain B]
variable [IsFractionRing A K] [IsIntegralClosure B A L] [IsFractionRing B L]
variable [FiniteDimensional K L] [IsSeparable K L]

open nonZeroDivisors IsLocalization Matrix Algebra

/-- Under the AKLB setting, `Iᵛ := traceDual A K (I : Submodule B L)` is the
`Submodule B L` such that `x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x, y) ∈ A` -/
def Submodule.traceDual (I : Submodule B L) : Submodule B L where
  carrier := { s | ∀ a ∈ I, traceForm K L s a ∈ (algebraMap A K).range }
  add_mem' hx hy a ha :=
    BilinForm.add_left (B := traceForm K L) _ _ _ ▸ add_mem (hx a ha) (hy a ha)
  zero_mem' a _ := BilinForm.zero_left (B := traceForm K L) a ▸ zero_mem _
  smul_mem' c x hx a ha := by
    rw [traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

variable {A K}

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

namespace Submodule

lemma mem_traceDual {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range :=
  Iff.rfl

lemma le_traceDual_iff_map_le_one {I J : Submodule B L} :
    I ≤ Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map
      ((trace K L).restrictScalars A) ≤ 1 := by
  rw [Submodule.map_le_iff_le_comap, Submodule.restrictScalars_mul, Submodule.mul_le]
  simp [SetLike.le_def, traceDual]

lemma le_traceDual_mul_iff {I J J' : Submodule B L} :
    I ≤ (J * J')ᵛ ↔ I * J ≤ J'ᵛ := by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]

lemma le_traceDual {I J : Submodule B L} :
    I ≤ Jᵛ ↔ I * J ≤ 1ᵛ := by
  rw [← le_traceDual_mul_iff, mul_one]

lemma le_traceDual_comm {I J : Submodule B L} :
    I ≤ Jᵛ ↔ J ≤ Iᵛ := by rw [le_traceDual, mul_comm, ← le_traceDual]

lemma le_traceDual_traceDual {I : Submodule B L} :
    I ≤ Iᵛᵛ := le_traceDual_comm.mpr le_rfl

end Submodule

open Submodule

variable [IsIntegrallyClosed A]

lemma Submodule.mem_traceDual_iff_isIntegral {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, IsIntegral A (traceForm K L x a) :=
  forall₂_congr (fun _ _ ↦ IsIntegrallyClosed.isIntegral_iff.symm)

/-- If `b` is an `A`-integral basis of `L` with discriminant `b`, then `d • a * x` is integral over
  `A` for all `a ∈ I` and `x ∈ Iᵛ`. -/
lemma isIntegral_discr_mul_of_mem_traceDual
    (I : Submodule B L) {ι} [DecidableEq ι] [Fintype ι]
    {b : Basis ι K L} (hb : ∀ i, IsIntegral A (b i))
    {a x : L} (ha : a ∈ I) (hx : x ∈ Iᵛ) :
    IsIntegral A ((discr K b) • a * x) := by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => trace K L (x * a * b i)
  have : Function.HasLeftInverse (traceMatrix K b).mulVec :=
    ⟨(traceMatrix K b)⁻¹.mulVec, fun v ↦ by simp [nonsing_inv_mul _ hinv]⟩
  rw [← traceMatrix_of_basis_mulVec, ← mulVec_smul, this.injective.eq_iff,
    traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _), b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc, b.equivFun.map_smul, discr_def, mul_comm, ← H, Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intros j k
  rw [updateColumn_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm, ← hy, ← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

lemma Submodule.traceDual_eq_span_dualBasis {ι} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) :
    (Submodule.span A (Set.range b))ᵛ =
      Submodule.span A (Set.range ((Algebra.traceForm K L).dualBasis
        (traceForm_nondegenerate K L) b)) := by
  apply le_antisymm
  · intros x hx
    rw [← ((Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b).sum_repr x]
    apply sum_mem
    rintro i -
    obtain ⟨a, ha : _ = Algebra.trace K L (x * b i)⟩ :=
      hx (b i) (Submodule.subset_span (Set.mem_range_self _))
    simp only [BilinForm.dualBasis_repr_apply, traceForm_apply, ← ha, algebraMap_smul]
    apply Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self _))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ a ha
    rw [← Fintype.range_total (S := A) A] at ha
    obtain ⟨v, rfl⟩ := ha
    rw [Fintype.total_apply, traceForm_apply, Finset.mul_sum, map_sum]
    apply sum_mem
    rintro i -
    rw [mul_comm, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_comm, ← traceForm_apply,
      BilinForm.apply_dualBasis_left, ← SetLike.mem_coe, RingHom.coe_range, ← Algebra.coe_bot]
    refine (⊥ : Subalgebra A K).smul_mem ?_ (v i)
    split; exact one_mem _; exact zero_mem _

variable (A K)

open scoped Classical

/-- The dual of a non-zero fractional ideal is the dual of the submodule under the traceform. -/
noncomputable
def FractionalIdeal.dual (I : FractionalIdeal B⁰ L) :
    FractionalIdeal B⁰ L :=
  if hI : I = 0 then 0 else
  ⟨Iᵛ, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), fun z hz ↦ ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, RingHom.map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · convert isIntegral_discr_mul_of_mem_traceDual I hb hx' hz using 1
      · ext w; exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, RingHom.map_mul, hy, ← Algebra.smul_def]⟩

variable {A K}

lemma FractionalIdeal.coe_dual {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) :
    (dual A K I : Submodule B L) = Iᵛ := by rw [dual, dif_neg hI]; rfl

@[simp]
lemma FractionalIdeal.coe_dual_one :
    (dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L) = 1ᵛ := by
  rw [← coe_one, coe_dual]
  exact one_ne_zero

@[simp]
lemma FractionalIdeal.dual_zero :
    dual A K (0 : FractionalIdeal B⁰ L) = 0 := by rw [dual, dif_pos rfl]

lemma FractionalIdeal.mem_dual {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) {x} :
    x ∈ dual A K I ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range := by
  rw [dual, dif_neg hI]; rfl

lemma FractionalIdeal.dual_ne_zero {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) :
    dual A K I ≠ 0 := by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b ∈ dual A K I by
    intro e
    rw [e, mem_zero_iff, ← (algebraMap B L).map_zero,
      (IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  rw [mem_dual hI]
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

@[simp]
lemma FractionalIdeal.dual_eq_zero_iff {I : FractionalIdeal B⁰ L} :
    dual A K I = 0 ↔ I = 0 := ⟨not_imp_not.mp dual_ne_zero, fun e ↦ e.symm ▸ dual_zero⟩

lemma FractionalIdeal.dual_ne_zero_iff {I : FractionalIdeal B⁰ L} :
    dual A K I ≠ 0 ↔ I ≠ 0 := dual_eq_zero_iff.not

lemma FractionalIdeal.le_dual_inv_aux {I J : FractionalIdeal B⁰ L} (hI : I ≠ 0) (hIJ : I * J ≤ 1) :
    J ≤ dual A K I := by
  rw [dual, dif_neg hI]
  intro x hx y hy
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

lemma FractionalIdeal.one_le_dual_one :
    1 ≤ dual A K (1 : FractionalIdeal B⁰ L) :=
  FractionalIdeal.le_dual_inv_aux one_ne_zero (by rw [one_mul])

lemma one_le_traceDual_one :
    (1 : Submodule B L) ≤ 1ᵛ := by
  rw [← FractionalIdeal.coe_one, ← FractionalIdeal.coe_dual, FractionalIdeal.coe_le_coe]
  exact FractionalIdeal.one_le_dual_one
  exact one_ne_zero

lemma FractionalIdeal.le_dual_iff {I J : FractionalIdeal B⁰ L} (hJ : J ≠ 0) :
    I ≤ dual A K J ↔ I * J ≤ dual A K 1 := by
  by_cases hI : I = 0
  · simp [hI, zero_le]
  rw [← coe_le_coe, ← coe_le_coe, coe_mul, coe_dual hJ, coe_dual_one, le_traceDual]

variable [IsDedekindDomain B] [IsFractionRing B L]

lemma FractionalIdeal.inv_le_dual (I : FractionalIdeal B⁰ L) :
    I⁻¹ ≤ dual A K I :=
  if hI : I = 0 then by simp [hI] else le_dual_inv_aux hI (le_of_eq (mul_inv_cancel hI))

lemma FractionalIdeal.dual_inv_le (I : FractionalIdeal B⁰ L) :
    (dual A K I)⁻¹ ≤ I := by
  by_cases hI : I = 0; · simp [hI]
  convert mul_right_mono ((dual A K I)⁻¹)
    (mul_left_mono I (FractionalIdeal.inv_le_dual (A := A) (K := K) I)) using 1
  · simp only [mul_inv_cancel hI, one_mul]
  · simp only [mul_inv_cancel (FractionalIdeal.dual_ne_zero (hI := hI)), mul_assoc, mul_one]

lemma FractionalIdeal.dual_eq_mul_inv (I : FractionalIdeal B⁰ L) :
    dual A K I = dual A K 1 * I⁻¹ := by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · suffices : dual A K I * I ≤ dual A K 1
    · convert mul_right_mono I⁻¹ this using 1; simp only [mul_inv_cancel hI, mul_one, mul_assoc]
    rw [← le_dual_iff hI]
  rw [le_dual_iff hI, mul_assoc, inv_mul_cancel hI, mul_one]

lemma FractionalIdeal.dual_mul_self {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) :
    dual A K I * I = dual A K 1 := by
  rw [dual_eq_mul_inv, mul_assoc, inv_mul_cancel hI, mul_one]

lemma FractionalIdeal.self_mul_dual (I : FractionalIdeal B⁰ L) (hI : I ≠ 0) :
    I * dual A K I = dual A K 1 := by
  rw [mul_comm, dual_mul_self hI]

lemma FractionalIdeal.dual_inv (I : FractionalIdeal B⁰ L) :
    dual A K I⁻¹ = dual A K 1 * I := by rw [dual_eq_mul_inv, inv_inv]

@[simp]
lemma FractionalIdeal.dual_dual (I : FractionalIdeal B⁰ L) :
    dual A K (dual A K I) = I := by
  rw [dual_eq_mul_inv, dual_eq_mul_inv I, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

lemma FractionalIdeal.dual_involutive :
    Function.Involutive (dual A K : FractionalIdeal B⁰ L → FractionalIdeal B⁰ L) := dual_dual

lemma FractionalIdeal.dual_injective :
    Function.Injective (dual A K : FractionalIdeal B⁰ L → FractionalIdeal B⁰ L) :=
  dual_involutive.injective

@[simp]
lemma FractionalIdeal.dual_le_dual {I J : FractionalIdeal B⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0) :
    dual A K I ≤ dual A K J ↔ J ≤ I := by
  nth_rewrite 2 [← dual_dual (A := A) (K := K) I]
  rw [le_dual_iff hJ, le_dual_iff (I := J), mul_comm]
  rwa [dual_ne_zero_iff]
