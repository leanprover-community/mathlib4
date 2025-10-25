/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.Qify

/-!

# (Absolute) Discriminant and Different Ideal

## Main results
- `NumberField.absNorm_differentIdeal`:
  The norm of `differentIdeal ℤ 𝒪` is the absolute discriminant.

-/

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

open nonZeroDivisors

lemma NumberField.absNorm_differentIdeal [Module.Free ℤ 𝒪] [IsDedekindDomain 𝒪] :
    (differentIdeal ℤ 𝒪).absNorm = (discr K).natAbs := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  refine (differentIdeal ℤ 𝒪).toAddSubgroup.relIndex_top_right.symm.trans ?_
  rw [← Submodule.comap_map_eq_of_injective (f := Algebra.linearMap 𝒪 K)
    (FaithfulSMul.algebraMap_injective 𝒪 K) (differentIdeal ℤ 𝒪)]
  refine (AddSubgroup.relIndex_comap (IsLocalization.coeSubmodule K
    (differentIdeal ℤ 𝒪)).toAddSubgroup (algebraMap 𝒪 K).toAddMonoidHom ⊤).trans ?_
  have := FractionalIdeal.quotientEquiv (R := 𝒪) (K := K) 1 (differentIdeal ℤ 𝒪)
    (differentIdeal ℤ 𝒪)⁻¹ 1 (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
    (le_inv_of_le_inv₀ (by simp [pos_iff_ne_zero, differentIdeal_ne_bot])
      (by simpa using FractionalIdeal.coeIdeal_le_one)) one_ne_zero one_ne_zero
  have := Nat.card_congr this.toEquiv
  refine this.trans ?_
  rw [FractionalIdeal.coe_one, coeIdeal_differentIdeal (K := ℚ), inv_inv]
  let b := integralBasis K
  let b' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b
  have hb : Submodule.span ℤ (Set.range b) = (1 : Submodule 𝒪 K).restrictScalars ℤ := by
    ext
    let e := IsIntegralClosure.equiv ℤ (RingOfIntegers K) K 𝒪
    simpa [e.symm.exists_congr_left, e] using mem_span_integralBasis K
  qify
  refine (AddSubgroup.relIndex_eq_abs_det (1 : Submodule 𝒪 K).toAddSubgroup (FractionalIdeal.dual
    ℤ ℚ 1 : FractionalIdeal 𝒪⁰ K).coeToSubmodule.toAddSubgroup ?_ b b' ?_ ?_).trans ?_
  · rw [Submodule.toAddSubgroup_le, ← FractionalIdeal.coe_one]
    exact FractionalIdeal.one_le_dual_one ℤ ℚ (L := K) (B := 𝒪)
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, hb, Submodule.toIntSubmodule_toAddSubgroup]
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, ← LinearMap.BilinForm.dualSubmodule_span_of_basis, hb]
    simp
  · simp only [Module.Basis.det_apply, discr, Algebra.discr]
    rw [← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
    congr! 2
    ext i j
    simp [b', Module.Basis.toMatrix_apply, mul_comm (RingOfIntegers.basis K i),
      b, integralBasis_apply, ← map_mul, Algebra.trace_localization ℤ ℤ⁰]

lemma NumberField.discr_mem_differentIdeal [Module.Free ℤ 𝒪] [IsDedekindDomain 𝒪] :
    ↑(discr K) ∈ differentIdeal ℤ 𝒪 := by
  have := (differentIdeal ℤ 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal (K := K), ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal (K := K), ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

lemma NumberField.not_dvd_discr_iff_forall_liesOver {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsMaximal), P.LiesOver (.span {p}) →
      Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module 𝒪 K
  simp_rw [← not_dvd_differentIdeal_iff]
  constructor
  · intro H P hP hP' hP''
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hP'')
    rw [absNorm_differentIdeal (K := K), ← Ideal.pow_inertiaDeg_eq_absNorm P hp,
      ← Int.natAbs_pow, Int.natAbs_dvd_natAbs] at this
    exact H (.trans (dvd_pow_self _ (Ideal.inertiaDeg_pos' ..).ne') this)
  · intro H h
    rw [← Int.dvd_natAbs, ← absNorm_differentIdeal (𝒪 := 𝒪)] at h
    obtain ⟨P, hP, h₁, h₂⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm hp _ h
    exact H P hP ⟨h₁.symm⟩ h₂

attribute [local simp] Ideal.span_le in
lemma NumberField.not_dvd_discr_iff_forall_mem {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module 𝒪 K
  have h := (Ideal.isPrime_of_prime
    (Ideal.prime_span_singleton_iff.mpr hp)).isMaximal (by simp [hp.ne_zero])
  rw [NumberField.not_dvd_discr_iff_forall_liesOver (𝒪 := 𝒪) hp]
  exact ⟨fun H P hP _ ↦ H P (hP.isMaximal (by aesop)) ⟨h.eq_of_le Ideal.IsPrime.ne_top' (by simpa)⟩,
    fun H P _ h ↦ H P _ (h.1.le (Ideal.mem_span_singleton_self _))⟩
