/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Unramified.Dedekind

/-!
# Every number field has a ramified prime over `ℚ`
...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/
@[expose] public section

section

variable (A B C G : Type*) [Group G] (H : Subgroup G) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup H B C]
  (q : Ideal B) (r : Ideal C) [r.LiesOver q]

theorem foo₁ : r.inertia H = (r.inertia G).subgroupOf H := rfl

variable [H.Normal] [FaithfulSMul B C] [FaithfulSMul A C] [IsDomain C] [Finite G]

example :
    letI := IsGaloisGroup.mulSemiringActionQuotient G B C H
    IsGaloisGroup (G ⧸ H) A B := by
  let := IsGaloisGroup.mulSemiringActionQuotient G B C H
  let := IsGaloisGroup.mulSemiringActionOfNormal G B C H
  let := IsGaloisGroup.smulCommClassQuotient G A B C H
  exact IsGaloisGroup.quotient G A B C H

theorem foo₃ {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (f : G →* G') :
    Nat.card (H ⊓ f.ker :) * Nat.card (H.map f) = Nat.card H := by
  have := f.restrict H
  have := Subgroup.index_ker (f.restrict H)
  rw [MonoidHom.restrict_range, MonoidHom.ker_restrict] at this
  sorry

lemma card_inertia_eq_ramificationIdxIn {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField]
    (G : Type*) [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  sorry

include A in
theorem foo₂ [IsDomain A] [IsDomain B]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.Flat A B] [Module.Flat A C] [Module.Flat B C]
    [q.IsPrime] [r.IsPrime] [PerfectField (r.under A).ResidueField] [PerfectField q.ResidueField] :
    letI := IsGaloisGroup.mulSemiringActionQuotient G B C H
    q.inertia (G ⧸ H) = (r.inertia G).map (QuotientGroup.mk' H) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro - ⟨g, hg, rfl⟩
    intro b
    simp
    specialize hg (algebraMap B C b)
    simp at hg
    rw [← IsGaloisGroup.algebraMap_smulOfNormal G B C H g b, ← map_sub] at hg
    rwa [← Ideal.mem_under, ← Ideal.over_def r q] at hg
  · apply Nat.le_of_dvd Nat.card_pos
    let p := r.under A
    have : q.LiesOver p := by
      rw [Ideal.liesOver_iff, Ideal.over_def r q, Ideal.under_under]
    let := IsGaloisGroup.mulSemiringActionQuotient G B C H
    let : MulSemiringAction G B := IsGaloisGroup.mulSemiringActionOfNormal G B C H
    let : SMulCommClass (G ⧸ H) A B := IsGaloisGroup.smulCommClassQuotient G A B C H
    have : IsGaloisGroup (G ⧸ H) A B := IsGaloisGroup.quotient G A B C H
    have := foo₃ (r.inertia G) (QuotientGroup.mk' H)
    simp only [QuotientGroup.ker_mk'] at this
    have h1 := card_inertia_eq_ramificationIdxIn p r G
    have h2 := card_inertia_eq_ramificationIdxIn p q (G ⧸ H)
    have h3 := card_inertia_eq_ramificationIdxIn q r H
    rw [h2]
    rw [h1] at this
    have key : Nat.card ↥(r.inertia G ⊓ H) = Nat.card ↥(r.inertia H) := by
      have : (r.inertia G).subgroupOf H = r.inertia H :=
        AddSubgroup.subgroupOf_inertia r.toAddSubgroup H
      rw [← this]
      transitivity (Nat.card <| ((r.inertia G).subgroupOf H).map H.subtype)
      · simp
      · apply Subgroup.card_map_of_injective
        exact H.subtype_injective
    rw [key, h3] at this
    sorry

end

open scoped NumberField nonZeroDivisors

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

/-- If `K` is a number field with positive rank, then there exists some maximal ideal of `𝓞 K`
that is ramified over `ℤ`. -/
lemma NumberField.exists_not_isUnramifiedAt_int (H : Module.finrank ℚ K ≠ 1) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  have := Module.finrank_pos (R := ℚ) (M := K)
  have := NumberField.abs_discr_gt_two (K := K) (by lia)
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  have := (not_dvd_discr_iff_forall_mem K 𝒪 hq).not_right.mp hqK
  push Not at this
  obtain ⟨P, hP, h, H⟩ := this
  exact ⟨P, hP.isMaximal (by aesop), H⟩

/-- Any number field that is unramified over `ℚ` has rank `1`. -/
lemma NumberField.finrank_eq_one_of_unramified [Algebra.Unramified ℤ 𝒪] :
    Module.finrank ℚ K = 1 := by
  by_contra H
  obtain ⟨P, _, H⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

/-- If `𝒪` is a domain that is a finite and unramified extension of `ℤ`, then `𝒪 = ℤ`. -/
lemma bijective_algebraMap_int_of_finite_of_unramified
    [Module.Finite ℤ 𝒪] [Algebra.Unramified ℤ 𝒪] [IsDomain 𝒪] [FaithfulSMul ℤ 𝒪] :
    Function.Bijective (algebraMap ℤ 𝒪) := by
  have := isDedekindDomain.of_formallyUnramified ℤ 𝒪
  let K := FractionRing 𝒪
  let : Algebra ℤ K := Ring.toIntAlgebra K
  have : CharZero 𝒪 := Algebra.charZero_of_charZero ℤ _
  have : NumberField K := { to_finiteDimensional := Module.Finite.of_isLocalization ℤ 𝒪 ℤ⁰ }
  have := NumberField.finrank_eq_one_of_unramified (K := K) (𝒪 := 𝒪)
  have : IsIntegralClosure ℤ ℤ K := .of_algEquiv _ (.ofBijective (IsScalarTower.toAlgHom _ _ _)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp this)) (by simp)
  exact bijective_algebraMap_of_linearEquiv (IsIntegralClosure.equiv ℤ ℤ K 𝒪).toLinearEquiv

/-- If `K` is a number field with positive rank such that `K/ℚ` is galois, then there exists
some rational prime `p : ℕ` such that every prime of `K` over `p` is ramified. -/
lemma NumberField.exists_not_isUnramifiedAt_int_of_isGalois [IsGalois ℚ K]
    (H : 1 < Module.finrank ℚ K) :
    ∃ p : ℕ, p.Prime ∧ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P → ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : MulSemiringAction Gal(K/ℚ) 𝒪 := IsIntegralClosure.MulSemiringAction ℤ ℚ K 𝒪
  have := IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ 𝒪 ℚ K
  obtain ⟨P, _, hP'⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H.ne'
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 ↦ Ideal.IsMaximal.ne_bot_of_isIntegral_int _
    (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by aesop)))
  have : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp this, fun Q _ hQ ↦ ?_⟩
  replace hQ : (p : 𝒪) ∈ Q := Q.mem_of_dvd
    (map_dvd (algebraMap _ _) p.associated_natAbs.symm.dvd) (by simpa using hQ)
  have : .span {p} = Ideal.under ℤ Q :=
    ((Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' this).mpr hQ).1
  rwa [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (by aesop),
    ← Ideal.ramificationIdxIn_eq_ramificationIdx _ _ Gal(K/ℚ), ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/ℚ),
    ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain (Ideal.IsMaximal.ne_bot_of_isIntegral_int _)]

open IsGaloisGroup NumberField -- probably should become a namespace

instance {I : Ideal ℤ} [I.IsPrime] : PerfectField I.ResidueField :=
  sorry

section

variable (G A B C : Type*) [Group G]
    [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B]
    [Algebra A C] [Algebra B C] [FaithfulSMul A C] [FaithfulSMul B C] [IsScalarTower A B C]

theorem NumberField.supr_inertia_eq_top (S G : Type*) [CommRing S] [Module.Finite ℤ S]
    [IsDomain S] [FaithfulSMul ℤ S] [Group G] [MulSemiringAction G S] [IsGaloisGroup G ℤ S] :
    ⨆ m : PrimeSpectrum S, m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have := IsGaloisGroup.finite G ℤ S
  let H : Subgroup G := ⨆ m : PrimeSpectrum S, m.asIdeal.toAddSubgroup.inertia G
  let R : Subalgebra ℤ S := FixedPoints.subalgebra ℤ S H
  have : Module.Finite ℤ R := Module.IsNoetherian.finite ℤ R.toSubmodule
  suffices h5 : Algebra.Unramified ℤ R by
    have h4 : Function.Bijective (algebraMap ℤ R) :=
      @bijective_algebraMap_int_of_finite_of_unramified R _ _ h5 _ _
    rw [← IsGaloisGroup.fixingSubgroup_range_algebraMap G ℤ ℤ S ⊤,
      IsScalarTower.algebraMap_eq ℤ R S, RingHom.coe_comp, h4.surjective.range_comp,
      IsGaloisGroup.fixingSubgroup_range_algebraMap G ℤ R S H]
  rw [Algebra.unramified_iff_forall]
  rintro ⟨mR, hmR⟩
  simp only
  rw [← Ideal.ramificationIdx'_eq_one_iff]
  have : H.Normal := sorry
  let := mulSemiringActionQuotient G R S H
  have : IsGaloisGroup (G ⧸ H) ℤ R := by
    let := mulSemiringActionOfNormal G R S H
    exact IsGaloisGroup.quotient G ℤ R S H
  have : mR.ramificationIdx' ℤ = Nat.card (Ideal.inertia (G ⧸ H) mR) := sorry -- Flat over ℤ
  rw [this, Subgroup.card_eq_one]
  have : Algebra.IsIntegral R S := IsGaloisGroup.isInvariant.isIntegral R S H
  obtain ⟨mS, hmS, hmRS⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := R) (S := S) mR (by simp)
  replace hmRS : mS.LiesOver mR := ⟨hmRS.symm⟩
  have : Module.Finite R S := sorry
  have : Module.Flat R S := sorry -- this is a problem...
  have : PerfectField mR.ResidueField := sorry
  rw [foo₂ ℤ R S G H mR mS, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  apply le_iSup_of_le ⟨mS, hmS⟩
  rfl

theorem NumberField.supr_inertia_eq_top' (K : Type*) [Field K] [NumberField K]
    (G : Type*) [Group G] [MulSemiringAction G K] [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have : Finite G := IsGaloisGroup.finite G ℚ K
  set H : Subgroup G := ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H
  have : IsGaloisGroup H (𝓞 F) (𝓞 K) := instIsGaloisGroupRingOfIntegersOfNumberField F K H
  suffices h : ∀ (m : Ideal (𝓞 F)) (hm : m.IsMaximal), Algebra.IsUnramifiedAt ℤ m by
    rw [eq_top_iff, ← fixingSubgroup_fixedPoints G ℚ K H, ← le_fixedPoints_iff_le_fixingSubgroup,
      fixedPoints_top, le_bot_iff, ← IntermediateField.finrank_eq_one_iff]
    contrapose! h
    exact NumberField.exists_not_isUnramifiedAt_int h
  intro mF hmF
  have hmF0 : mF ≠ ⊥ := hmF.ne_bot_of_isIntegral_int
  obtain ⟨mK, hmK, ⟨rfl⟩⟩ := mF.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K)
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hmF0, Ideal.under_under]
  have hm1 := Ideal.IsMaximal.ne_bot_of_isIntegral_int (mK.under ℤ)
  have h : mK.toAddSubgroup.inertia G ≤ H :=
    le_iSup (fun m : MaximalSpectrum (𝓞 K) ↦ m.asIdeal.toAddSubgroup.inertia G) ⟨mK, hmK⟩
  replace h : Nat.card (mK.toAddSubgroup.inertia H) = Nat.card (mK.toAddSubgroup.inertia G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h, Subgroup.card_subtype,
      AddSubgroup.subgroupOf_inertia]
  let := Ideal.Quotient.field mK
  let := Ideal.Quotient.field (mK.under (𝓞 F))
  let := Ideal.Quotient.field (mK.under ℤ)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) (mK.under (𝓞 F)) hmF0 mK,
    Ideal.card_inertia_eq_ramificationIdxIn (G := G) (mK.under ℤ) hm1 mK,
    Ideal.ramificationIdxIn_eq_ramificationIdx (mK.under (𝓞 F)) mK H,
    Ideal.ramificationIdxIn_eq_ramificationIdx (mK.under ℤ) mK G] at h
  have key := Ideal.ramificationIdx_algebra_tower (Ideal.map_ne_bot_of_ne_bot hmF0)
    (Ideal.map_ne_bot_of_ne_bot hm1) Ideal.map_comap_le
  rwa [h, right_eq_mul₀ (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver mK hm1)] at key
