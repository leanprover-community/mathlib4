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

open Pointwise in
theorem foo₄ (B C G : Type*) [Group G] (H : Subgroup G) [CommRing B] [CommRing C]
    [Algebra B C] [MulSemiringAction G C] [IsGaloisGroup H B C]
    [H.Normal] [FaithfulSMul B C] [IsDomain C] [Finite H]
    (q : Ideal B) (r : Ideal C) [r.LiesOver q] [r.IsPrime] :
    letI := IsGaloisGroup.mulSemiringActionQuotient G B C H
    q.inertia (G ⧸ H) = (r.inertia G).map (QuotientGroup.mk' H) := by
  have : IsDomain B := IsDomain.of_faithfulSMul B C
  let := IsGaloisGroup.mulSemiringActionQuotient G B C H
  apply le_antisymm; swap
  · rintro - ⟨g, hg, rfl⟩ b
    specialize hg (algebraMap B C b)
    rw [← IsGaloisGroup.algebraMap_smulOfNormal G B C H g b, ← map_sub] at hg
    rwa [Submodule.mem_toAddSubgroup, QuotientGroup.mk'_apply, r.over_def q, r.mem_under B]
  · -- let `g : G ⧸ H` be an element of the inertia subgroup of `q`
    intro g hg
    -- first we will find a lift `g' : G` in the decomposition subgroup of `r`
    have mem_decomposition : ∃ g' : MulAction.stabilizer G r, QuotientGroup.mk' H g' = g := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H g
      have : (g • r).under B = r.under B := by
        replace hg := Ideal.inertia_le_stabilizer q hg
        rw [MulAction.mem_stabilizer_iff] at hg
        simp at hg
        rw [← Ideal.over_def r q, ← hg, Ideal.over_def r q]
        rw [Ideal.under_def, Ideal.pointwise_smul_eq_comap]
        nth_rw 2 [← Ideal.comap_coe]
        rw [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, Ideal.under_def]
        nth_rw 2 [← Ideal.comap_coe]
        rw [Ideal.comap_comap]
        congr
        ext x
        let := IsGaloisGroup.mulSemiringActionOfNormal G B C H
        have : SMulDistribClass G B C := IsGaloisGroup.smulDistribClass_smulOfNormal G B C H
        simp [IsGaloisGroup.mulSemiringActionQuotient_smul_def]
        change g⁻¹ • (algebraMap B C) x = (algebraMap B C) (↑(g⁻¹ : G) • x)
        exact Eq.symm (algebraMap.coe_smul' g⁻¹ x C)
      obtain ⟨g', hg'⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B C H (g • r) r this
      exact ⟨⟨g' * g, by simpa [mul_smul, eq_comm]⟩, by simp⟩
    -- and now we must find a lift `g' : G` in the inertia subgroup of `r`
    obtain ⟨g, rfl⟩ := mem_decomposition
    let φ : (C ⧸ r) ≃ₐ[B ⧸ q] (C ⧸ r) :=
    { __ := Ideal.Quotient.stabilizerHom r (r.under ℤ) G g
      commutes' := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        specialize hg x
        simp
        rw [IsScalarTower.algebraMap_apply B C (C ⧸ r), Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.stabilizerHom_apply, Ideal.Quotient.eq]
        simp [Ideal.over_def r q] at hg
        convert hg
        let := IsGaloisGroup.mulSemiringActionOfNormal G B C H
        have : SMulDistribClass G B C := IsGaloisGroup.smulDistribClass_smulOfNormal G B C H
        rw [IsGaloisGroup.mulSemiringActionQuotient_smul_def]
        simp [Subgroup.smul_def] }
    obtain ⟨g', hg'⟩ := Ideal.Quotient.stabilizerHom_surjective H q r φ
    let v : MulAction.stabilizer G r := ⟨g', g'.2⟩⁻¹ * g
    refine ⟨v, ?_, by simp [v]⟩
    have := Ideal.Quotient.ker_stabilizerHom r (r.under ℤ) G
    rw [SetLike.ext_iff] at this
    specialize this v
    refine this.mp ?_
    simp [v, inv_mul_eq_one]
    ext x
    change Ideal.Quotient.stabilizerHom r q H g' x = _
    rw [hg']
    rfl

end

section

-- PRed
instance {A B : Type*} [CommRing A] [CommRing B] (h : A ≃+* B) :
    letI := h.toRingHom.toAlgebra
    Module.Finite A B :=
  h.finite

-- PRed
theorem PerfectField.of_ringEquiv {K L : Type*} [Field K] [Field L] (h : K ≃+* L) [PerfectField K] :
    PerfectField L := by
  let := h.toRingHom.toAlgebra
  exact Algebra.IsAlgebraic.perfectField (K := K)

-- PRed
instance (R : Type*) [CommRing R] [IsDomain R] : IsFractionRing R (⊥ : Ideal R).ResidueField :=
  IsLocalization.of_ringEquiv_left (RingEquiv.quotientBot R).symm
    (MulEquivClass.map_nonZeroDivisors (RingEquiv.quotientBot R).symm) (by simp)

instance (R : Type*) [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]
    [PerfectField (FractionRing R)] (P : Ideal R) [P.IsPrime] : PerfectField P.ResidueField := by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R (⊥ : Ideal R).ResidueField).toRingEquiv
  · suffices Finite P.ResidueField from inferInstance
    have : P.IsMaximal := ‹P.IsPrime›.isMaximal hP
    have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    let : Field (R ⧸ P) := Ideal.Quotient.field P
    exact .of_equiv (R ⧸ P) (IsFractionRing.algEquiv (R ⧸ P) (R ⧸ P) P.ResidueField).toEquiv

-- in the big refactor PR
lemma card_inertia_eq_ramificationIdxIn {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField]
    (G : Type*) [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  sorry

instance (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] (q : Ideal B) (r : Ideal C) [r.LiesOver q] :
    r.LiesOver (q.under A) :=
  Ideal.LiesOver.trans r q (q.under A)

instance (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] (q : Ideal B) (r : Ideal C) [r.LiesOver q] :
    q.LiesOver (r.under A) :=
  Ideal.LiesOver.tower_bot r q (r.under A)

end

section

variable (A B C G : Type*) [Group G] (H : Subgroup G) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup H B C]
  (q : Ideal B) (r : Ideal C) [r.LiesOver q]

variable [H.Normal] [FaithfulSMul B C] [FaithfulSMul A C] [IsDomain C] [Finite G]

theorem foo₃ {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (f : G →* G') :
    Nat.card (f.ker ⊓ H : Subgroup G) * Nat.card (H.map f) = Nat.card H := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective H.subtype_injective,
    ← f.ker_restrict, ← f.restrict_range, ← Subgroup.index_ker, Subgroup.card_mul_index]

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
  rw [← Ideal.ramificationIdx'_eq_one_iff]
  have : H.Normal := sorry
  let := mulSemiringActionQuotient G R S H
  have : IsGaloisGroup (G ⧸ H) ℤ R := by
    let := mulSemiringActionOfNormal G R S H
    exact IsGaloisGroup.quotient G ℤ R S H
  have : mR.ramificationIdx' ℤ = Nat.card (Ideal.inertia (G ⧸ H) mR) := by
    rw [card_inertia_eq_ramificationIdxIn (mR.under ℤ) mR (G ⧸ H)]
    -- will be solved after the `ramificationIdxIn` refactor
    sorry
  rw [this, Subgroup.card_eq_one]
  have : Algebra.IsIntegral R S := IsGaloisGroup.isInvariant.isIntegral R S H
  obtain ⟨mS, hmS, hmRS⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := R) (S := S) mR (by simp)
  replace hmRS : mS.LiesOver mR := ⟨hmRS.symm⟩
  rw [foo₄ R S G H mR mS, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
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
