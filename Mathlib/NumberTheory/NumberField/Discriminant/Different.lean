/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Tactic.Qify

/-!

# (Absolute) Discriminant and Different Ideal

## Main results
- `NumberField.absNorm_differentIdeal`:
  The norm of `differentIdeal ℤ 𝒪` is the absolute discriminant.
- `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`:
  Formula for the absolute discriminant `L` in terms of that of `K` in an extension `L/K`.

-/

namespace NumberField

variable (K 𝒪 : Type*) [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsFractionRing 𝒪 K] [IsIntegralClosure 𝒪 ℤ K] [IsDedekindDomain 𝒪] [CharZero 𝒪]
variable [Module.Finite ℤ 𝒪]

open nonZeroDivisors IntermediateField

lemma absNorm_differentIdeal : (differentIdeal ℤ 𝒪).absNorm = (discr K).natAbs := by
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

lemma discr_mem_differentIdeal : ↑(discr K) ∈ differentIdeal ℤ 𝒪 := by
  have := (differentIdeal ℤ 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal (K := K), ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal (K := K), ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

attribute [local instance] FractionRing.liftAlgebra in
theorem natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*) [Field L]
    [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractionRing 𝒪' L] [IsIntegralClosure 𝒪' ℤ L]
    [IsDedekindDomain 𝒪'] [CharZero 𝒪'] [Algebra K L] [Algebra 𝒪 𝒪'] [Algebra 𝒪 L]
    [IsScalarTower 𝒪 K L] [IsScalarTower 𝒪 𝒪' L] [NoZeroSMulDivisors 𝒪 𝒪'] [Module.Free ℤ 𝒪']
    [Module.Finite ℤ 𝒪'] [Module.Finite 𝒪 𝒪'] :
    (discr L).natAbs = Ideal.absNorm (differentIdeal 𝒪 𝒪') *
      (discr K).natAbs ^ Module.finrank K L := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ 𝒪 𝒪')
  rwa [absNorm_differentIdeal L, map_mul, Ideal.absNorm_algebraMap,
    absNorm_differentIdeal K, Algebra.finrank_eq_of_equiv_equiv
      (FractionRing.algEquiv 𝒪 K).toRingEquiv (FractionRing.algEquiv 𝒪' L).toRingEquiv] at this
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv 𝒪 K)
    (FractionRing.algEquiv 𝒪' L) _

theorem discr_dvd_discr (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    discr K ∣ discr L := by
  suffices discr K ^ Module.finrank K L ∣ discr L from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs, natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L),
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (discr K ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

end NumberField
