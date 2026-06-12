/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.LinearDisjoint
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!

# (Absolute) Discriminant and Different Ideal

## Main results
- `NumberField.absNorm_differentIdeal`:
  The norm of `differentIdeal ℤ 𝒪` is the absolute discriminant.
- `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`:
  Formula for the absolute discriminant of `L` in terms of that of `K` in an extension `L/K`.
- `NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`:
  Assume that `K₁` and `K₂` are two linear disjoint number fields with coprime different ideals.
  Then, the absolute value of the discriminant of their compositum is equal to
  `|discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`.

-/

public section

namespace NumberField

variable (K 𝒪 : Type*) [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]

open IntermediateField IsDedekindDomain

section

variable [IsFractionRing 𝒪 K] [IsDedekindDomain 𝒪] [CharZero 𝒪]
variable [Module.Finite ℤ 𝒪]

open nonZeroDivisors IntermediateField Module

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
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

attribute [local instance] FractionRing.liftAlgebra in
theorem natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*) [Field L]
    [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractionRing 𝒪' L] [IsIntegralClosure 𝒪' ℤ L]
    [IsDedekindDomain 𝒪'] [CharZero 𝒪'] [Algebra K L] [Algebra 𝒪 𝒪'] [Algebra 𝒪 L]
    [IsScalarTower 𝒪 K L] [IsScalarTower 𝒪 𝒪' L] [IsTorsionFree 𝒪 𝒪'] [Free ℤ 𝒪']
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

variable (L : Type*) [Field L]

theorem isCoprime_differentIdeal_of_isCoprime_discr {K₁ K₂ : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Algebra K₁ L] [Algebra K₂ L]
    (h : IsCoprime (discr K₁) (discr K₂)) :
    IsCoprime ((differentIdeal ℤ (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L)))
      ((differentIdeal ℤ (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L))) := by
  obtain ⟨u, v, h⟩ := h
  refine Ideal.isCoprime_iff_exists.mpr ⟨u * discr K₁, ?_, v * discr K₂, ?_, ?_⟩
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₁) (𝓞 L))]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₁) (𝓞 L)) <| discr_mem_differentIdeal _ _
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₂) (𝓞 L))]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₂) (𝓞 L)) <| discr_mem_differentIdeal _ _
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, h, Int.cast_one]

variable [NumberField L]

theorem discr_dvd_discr [Algebra K L] :
    discr K ∣ discr L := by
  suffices discr K ^ Module.finrank K L ∣ discr L from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs, natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L),
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (discr K ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

set_option backward.isDefEq.respectTransparency false in
/--
Let `K₁` and `K₂` be two number fields and assume that `K₁/ℚ` is Galois. If `discr K₁` and
`discr K₂` are coprime, then they are linear disjoint over `ℚ`.
-/
theorem linearDisjoint_of_isGalois_isCoprime_discr (K₁ K₂ : IntermediateField ℚ L) [IsGalois ℚ K₁]
    (h : IsCoprime (discr K₁) (discr K₂)) :
    K₁.LinearDisjoint K₂ := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(K₁ ⊓ K₂)) by
    contrapose! this
    have : 1 < Module.finrank ℚ ↥(K₁ ⊓ K₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', ?_⟩
      rwa [ne_eq, ← IntermediateField.finrank_eq_one_iff] at this
    exact Int.isUnit_iff_abs_eq.not.mpr <| by linarith [abs_discr_gt_two this]
  exact h.isUnit_of_dvd' (NumberField.discr_dvd_discr _ _) (NumberField.discr_dvd_discr _ _)

/--
Let `K₁` and `K₂` be two number fields and assume that their different ideals (over ℤ) are coprime.
Then, the absolute value of the discriminant of their compositum is equal to
`|discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`.
-/
theorem natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (K₁ K₂ : IntermediateField ℚ L)
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal ℤ (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L)))
      ((differentIdeal ℤ (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L)))) :
    (discr L).natAbs =
      (discr K₁).natAbs ^ Module.finrank ℚ K₂ * (discr K₂).natAbs ^ Module.finrank ℚ K₁ := by
  let _ : Algebra (FractionRing (𝓞 K₁)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have h_main := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K₂ (𝓞 K₂) L (𝓞 L)
  rwa [differentIdeal_eq_map_differentIdeal ℤ (𝓞 L) (𝓞 K₂) (𝓞 K₁) (F₁ := K₂) (F₂ := K₁)
    (by rwa [linearDisjoint_comm]) (by rwa [sup_comm]) (by rwa [isCoprime_comm]),
    Ideal.absNorm_algebraMap, absNorm_differentIdeal K₁, h₁.finrank_right_eq_finrank h₂,
    Algebra.finrank_eq_of_equiv_equiv (FractionRing.algEquiv _ K₁).toRingEquiv
    (FractionRing.algEquiv _ L).toRingEquiv, h₁.finrank_left_eq_finrank h₂] at h_main
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 K₁) K₁)
    (FractionRing.algEquiv (𝓞 L) L) _

end

/-- Also see `not_dvd_discr_iff_forall_mem` for a slightly easier to use RHS. -/
lemma not_dvd_discr_iff_forall_liesOver [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsMaximal), P.LiesOver (.span {p}) →
      Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  simp_rw [← not_dvd_differentIdeal_iff]
  contrapose!
  constructor
  · intro h
    rw [← Int.dvd_natAbs, ← absNorm_differentIdeal K 𝒪] at h
    obtain ⟨P, hP, h₁, h₂⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm hp _ h
    exact ⟨P, hP, ⟨h₁.symm⟩, h₂⟩
  · rintro ⟨P, hP, hP', hP''⟩
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hP'')
    rw [absNorm_differentIdeal K, Ideal.absNorm_eq_pow_inertiaDeg P hp,
      ← Int.natAbs_pow, Int.natAbs_dvd_natAbs] at this
    exact (dvd_pow_self _ (Ideal.inertiaDeg_pos' ..).ne').trans this

/-- Also see `not_dvd_discr_iff_forall_liesOver` for a slightly easier to prove RHS. -/
lemma not_dvd_discr_iff_forall_mem [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact ⟨fun H P hP h ↦ H P (hP.isMaximal (by aesop))
    ((Ideal.liesOver_span_iff hP.ne_top hp).mpr h),
    fun H P _ h ↦ H P _ (h.1.le (Ideal.mem_span_singleton_self _))⟩

end NumberField
