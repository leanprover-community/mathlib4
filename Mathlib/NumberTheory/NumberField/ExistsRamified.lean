/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.Unramified.Dedekind

/-!
# Every number field has a ramified prime over `ℚ`
...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/
@[expose] public section

section

-- PRed
open Pointwise in
instance (G R : Type*) [Group G] [CommRing R] [MulSemiringAction G R] :
    MulAction G (PrimeSpectrum R) where
  smul g P := ⟨g • P, P.2.smul g⟩
  mul_smul g h P := PrimeSpectrum.ext (mul_smul g h P.1)
  one_smul P := PrimeSpectrum.ext (one_smul G P.1)

-- PRed
open Pointwise in
@[simp]
theorem PrimeSpectrum.asIdeal_smul (G R : Type*) [Group G] [CommRing R] [MulSemiringAction G R]
    (g : G) (P : PrimeSpectrum R) : (g • P).asIdeal = g • P.asIdeal :=
  rfl

-- PRed
theorem Ideal.coe_mem_inertia (G : Type*) [Group G] (H : Subgroup G) (h : H)
    (R : Type*) [CommRing R] (I : Ideal R) [MulSemiringAction G R] :
    ↑h ∈ I.inertia G ↔ h ∈ I.inertia H :=
  .rfl

-- PRed
open Pointwise in
theorem Ideal.smul_under {G R S : Type*} [Group G] [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G R] [MulSemiringAction G S] [SMulDistribClass G R S]
    (g : G) (I : Ideal S) : g • I.under R = (g • I).under R := by
  simp_rw [Ideal.pointwise_smul_eq_comap, Ideal.under_def]
  nth_rw 1 [← Ideal.comap_coe]
  nth_rw 4 [← Ideal.comap_coe]
  simp_rw [Ideal.comap_comap]
  congr
  ext
  simp [algebraMap.smul']

-- PRed
open Pointwise in
instance {α β γ : Type*} [Monoid α] [Monoid β] [Semiring γ] [SMul α β] [MulSemiringAction α γ]
    [MulSemiringAction β γ] [IsScalarTower α β γ] : IsScalarTower α β (Ideal γ) where
  smul_assoc x y z := by
    simp_rw [Ideal.pointwise_smul_def, Ideal.map_map]
    congr
    ext
    simp

-- PRed
open Pointwise in
theorem Ideal.inertia_quotient (B C G : Type*) [Group G] (H : Subgroup G) [CommRing B] [CommRing C]
    [Algebra B C] [MulSemiringAction G C] [Algebra.IsInvariant B C H] [SMulCommClass H B C]
    [H.Normal] [MulSemiringAction (G ⧸ H) B]
    [MulSemiringAction G B] [IsScalarTower G (G ⧸ H) B] [SMulDistribClass G B C] [Finite H]
    (q : Ideal B) (r : Ideal C) [r.LiesOver q] [r.IsPrime] :
    q.inertia (G ⧸ H) = (r.inertia G).map (QuotientGroup.mk' H) := by
  apply le_antisymm; swap
  · rintro - ⟨g, hg, rfl⟩ b
    specialize hg (algebraMap B C b)
    rw [← algebraMap.smul', ← map_sub] at hg
    rwa [QuotientGroup.mk'_apply, MulAction.coe_quotient_smul, r.over_def q]
  · -- let `g : G ⧸ H` be an element of the inertia subgroup of `q`
    intro g hg
    -- first we will find a lift in the decomposition subgroup of `r`
    have mem_decomposition : ∃ g' : MulAction.stabilizer G r, QuotientGroup.mk' H g' = g := by
      replace hg := Ideal.inertia_le_stabilizer q hg
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H g
      rw [MulAction.mem_stabilizer_iff, QuotientGroup.mk'_apply, MulAction.coe_quotient_smul] at hg
      have : (g • r).under B = r.under B := by rwa [← Ideal.smul_under, ← Ideal.over_def r q]
      obtain ⟨g', hg'⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B C H (g • r) r this
      exact ⟨⟨g' * g, by simpa [mul_smul, eq_comm]⟩, by simp⟩
    -- and now a further modification will give a lift in the inertia subgroup of `r`
    obtain ⟨g, rfl⟩ := mem_decomposition
    let φ : (C ⧸ r) ≃ₐ[B ⧸ q] (C ⧸ r) :=
    { __ := Ideal.Quotient.stabilizerHom r (r.under ℤ) G g
      commutes' x := by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        specialize hg x
        rw [Submodule.mem_toAddSubgroup, QuotientGroup.mk'_apply, MulAction.coe_quotient_smul,
          Ideal.over_def r q, Ideal.mem_under, map_sub, algebraMap.smul'] at hg
        rwa [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.mk_algebraMap,
          IsScalarTower.algebraMap_apply B C (C ⧸ r), Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.stabilizerHom_apply, Ideal.Quotient.eq] }
    obtain ⟨g', hg'⟩ := Ideal.Quotient.stabilizerHom_surjective H q r φ
    let v := ⟨g', g'.2⟩⁻¹ * g
    refine ⟨v, ?_, by simp [v]⟩
    rw [SetLike.mem_coe, Ideal.coe_mem_inertia, ← Ideal.Quotient.ker_stabilizerHom r (r.under ℤ) G,
      MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    rwa [AlgEquiv.ext_iff] at hg' ⊢

end

section

-- PRed
instance (R : Type*) [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]
    [PerfectField (FractionRing R)] (P : Ideal R) [P.IsPrime] : PerfectField P.ResidueField := by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R (⊥ : Ideal R).ResidueField).toRingEquiv
  · suffices Finite P.ResidueField from inferInstance
    have : P.IsMaximal := ‹P.IsPrime›.isMaximal hP
    have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    let : Field (R ⧸ P) := Ideal.Quotient.field P
    exact .of_equiv (R ⧸ P) (IsFractionRing.algEquiv (R ⧸ P) (R ⧸ P) P.ResidueField).toEquiv

-- PRed
instance (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] (q : Ideal B) (r : Ideal C) [r.LiesOver q] :
    r.LiesOver (q.under A) :=
  Ideal.LiesOver.trans r q (q.under A)

-- PRed
instance (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] (q : Ideal B) (r : Ideal C) [r.LiesOver q] :
    q.LiesOver (r.under A) :=
  Ideal.LiesOver.tower_bot r q (r.under A)

end

open scoped nonZeroDivisors

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

namespace NumberField

/-- If `K` is a number field with positive rank, then there exists some maximal ideal of `𝓞 K`
that is ramified over `ℤ`. -/
lemma exists_not_isUnramifiedAt_int (H : Module.finrank ℚ K ≠ 1) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  have := Module.finrank_pos (R := ℚ) (M := K)
  have := abs_discr_gt_two (K := K) (by lia)
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  have := (not_dvd_discr_iff_forall_mem K 𝒪 hq).not_right.mp hqK
  push Not at this
  obtain ⟨P, hP, h, H⟩ := this
  exact ⟨P, hP.isMaximal (by aesop), H⟩

/-- Any number field that is unramified over `ℚ` has rank `1`. -/
lemma finrank_eq_one_of_unramified [Algebra.Unramified ℤ 𝒪] :
    Module.finrank ℚ K = 1 := by
  by_contra H
  obtain ⟨P, _, H⟩ := exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

/-- If `𝒪` is a domain that is a finite and unramified extension of `ℤ`, then `𝒪 = ℤ`. -/
lemma _root_.bijective_algebraMap_int_of_finite_of_unramified
    [Module.Finite ℤ 𝒪] [Algebra.Unramified ℤ 𝒪] [IsDomain 𝒪] [FaithfulSMul ℤ 𝒪] :
    Function.Bijective (algebraMap ℤ 𝒪) := by
  have := isDedekindDomain.of_formallyUnramified ℤ 𝒪
  let K := FractionRing 𝒪
  let : Algebra ℤ K := Ring.toIntAlgebra K
  have : CharZero 𝒪 := Algebra.charZero_of_charZero ℤ _
  have : NumberField K := { to_finiteDimensional := Module.Finite.of_isLocalization ℤ 𝒪 ℤ⁰ }
  have := finrank_eq_one_of_unramified (K := K) (𝒪 := 𝒪)
  have : IsIntegralClosure ℤ ℤ K := .of_algEquiv _ (.ofBijective (IsScalarTower.toAlgHom _ _ _)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp this)) (by simp)
  exact bijective_algebraMap_of_linearEquiv (IsIntegralClosure.equiv ℤ ℤ K 𝒪).toLinearEquiv

/-- If `K` is a number field with positive rank such that `K/ℚ` is galois, then there exists
some rational prime `p : ℕ` such that every prime of `K` over `p` is ramified. -/
lemma exists_not_isUnramifiedAt_int_of_isGalois [IsGalois ℚ K] (H : 1 < Module.finrank ℚ K) :
    ∃ p : ℕ, p.Prime ∧ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P → ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : MulSemiringAction Gal(K/ℚ) 𝒪 := IsIntegralClosure.MulSemiringAction ℤ ℚ K 𝒪
  have := IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ 𝒪 ℚ K
  obtain ⟨P, _, hP'⟩ := exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H.ne'
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 ↦ Ideal.IsMaximal.ne_bot_of_isIntegral_int _
    (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by aesop)))
  have : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp this, fun Q _ hQ ↦ ?_⟩
  replace hQ : (p : 𝒪) ∈ Q := Q.mem_of_dvd
    (map_dvd (algebraMap _ _) p.associated_natAbs.symm.dvd) (by simpa using hQ)
  have : .span {p} = Ideal.under ℤ Q :=
    ((Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' this).mpr hQ).1
  rwa [← Ideal.ramificationIdx'_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) _ Gal(K/ℚ), ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/ℚ), Ideal.ramificationIdx'_eq_one_iff]

open IsGaloisGroup Pointwise in
/-- A Galois group is generated by its inertia subgroups. -/
theorem supr_inertia_eq_top (S G : Type*) [CommRing S] [Module.Finite ℤ S]
    [IsDomain S] [FaithfulSMul ℤ S] [Group G] [MulSemiringAction G S] [IsGaloisGroup G ℤ S] :
    ⨆ m : PrimeSpectrum S, m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have := IsGaloisGroup.finite G ℤ S
  let H : Subgroup G := ⨆ m : PrimeSpectrum S, m.asIdeal.toAddSubgroup.inertia G
  let R : Subalgebra ℤ S := FixedPoints.subalgebra ℤ S H
  let : Algebra ℤ R := Ring.toIntAlgebra R
  have : Module.Finite ℤ R := Module.IsNoetherian.finite ℤ R.toSubmodule
  suffices Algebra.Unramified ℤ R by
    rw [← fixingSubgroup_range_algebraMap G ℤ ℤ S ⊤, IsScalarTower.algebraMap_eq ℤ R S,
      RingHom.coe_comp, bijective_algebraMap_int_of_finite_of_unramified.surjective.range_comp,
      fixingSubgroup_range_algebraMap G ℤ R S H]
  rw [Algebra.unramified_iff_forall]
  rintro ⟨mR, hmR⟩
  rw [← Ideal.ramificationIdx'_eq_one_iff]
  have : H.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    let e : PrimeSpectrum S ≃ PrimeSpectrum S := MulAction.toPerm g
    simp only [H]
    rw [Subgroup.map_iSup]
    conv_rhs => rw [← e.iSup_comp]
    apply iSup_congr
    intro P
    ext x
    simp [e, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    simp_rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq]
    simp only [↓existsAndEq, and_true]
    rw [← Equiv.forall_congr_right (MulAction.toPerm g⁻¹)]
    simp [mul_smul, smul_sub]
  let := mulSemiringActionQuotient G R S H
  have : IsGaloisGroup (G ⧸ H) ℤ R := by
    let := mulSemiringActionOfNormal G R S H
    exact IsGaloisGroup.quotient G ℤ R S H
  have : mR.ramificationIdx' ℤ = Nat.card (Ideal.inertia (G ⧸ H) mR) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (mR.under ℤ) mR (G := G ⧸ H),
      Ideal.ramificationIdxIn_eq_ramificationIdx (mR.under ℤ) mR (G ⧸ H)]
  rw [this, Subgroup.card_eq_one]
  have : Algebra.IsIntegral R S := IsGaloisGroup.isInvariant.isIntegral R S H
  obtain ⟨mS, hmS, hmRS⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := R) (S := S) mR (by simp)
  replace hmRS : mS.LiesOver mR := ⟨hmRS.symm⟩
  let := mulSemiringActionOfNormal G R S H
  rw [Ideal.inertia_quotient R S G H mR mS, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  apply le_iSup_of_le ⟨mS, hmS⟩
  rfl

end NumberField
