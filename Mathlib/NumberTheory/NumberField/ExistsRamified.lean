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
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Unramified.Dedekind

/-!
# Every number field has a ramified prime over `ℚ`
...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/
@[expose] public section

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
instance {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (p : Ideal (𝓞 K)) (q : Ideal (𝓞 L)) [q.LiesOver p] [q.IsMaximal] [p.IsMaximal] :
    Algebra.IsSeparable ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ q) := by
  sorry

instance {K : Type*} [Field K] [NumberField K]
    (p : Ideal ℤ) (q : Ideal (𝓞 K)) [q.LiesOver p] [q.IsMaximal] [p.IsMaximal] :
    Algebra.IsSeparable (ℤ ⧸ p) ((𝓞 K) ⧸ q) := by
  sorry

-- PRed
/-- Existing construction with `Finite G` replaced by `IsIntegral A B` -/
theorem IsGaloisGroup.to_isFractionRing'
    (G A B K L : Type*) [Group G] [CommRing A]
    [CommRing B] [MulSemiringAction G B] [Algebra A B] [Field K] [Field L]
    [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L] [IsFractionRing A K]
    [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L] [MulSemiringAction G L]
    [SMulDistribClass G B L]
    [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L := by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h ↦ ?_⟩, ⟨fun g x y ↦ ?_⟩, ⟨fun x h ↦ ?_⟩⟩
  · have := hGAB.faithful
    exact eq_of_smul_eq_smul fun y ↦ by simpa [← algebraMap.coe_smul'] using h (algebraMap B L y)
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective B y
    simp [Algebra.smul_def, smul_mul', smul_div₀', hc, ← algebraMap.coe_smul']
  · have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
    have : Nontrivial B := (IsFractionRing.nontrivial_iff_nontrivial B L).mpr inferInstance
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective B x
    have hy' : algebraMap B L y ≠ 0 := by simpa using nonZeroDivisors.ne_zero hy
    obtain ⟨b, a, ha, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) y).exists_smul_eq_mul x hy
    rw [mul_comm, Algebra.smul_def, mul_comm] at hb
    replace ha : (algebraMap B L) (algebraMap A B a) ≠ 0 := by simpa [← hc]
    have hxy : algebraMap B L x / algebraMap B L y =
      algebraMap B L b / algebraMap B L (algebraMap A B a) := by
      rw [div_eq_div_iff hy' ha, ← map_mul, hb, map_mul]
    obtain ⟨b, rfl⟩ := hGAB.isInvariant.isInvariant b
      (by simpa [ha, hxy, smul_div₀', ← algebraMap.coe_smul'] using h)
    use algebraMap A K b / algebraMap A K a
    simp [hc, div_eq_div_iff ha hy', ← map_mul, ← map_mul, hb]

namespace Ideal

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

-- PRed
theorem ramificationIdx'_eq_one [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : q.ramificationIdx' R = 1 := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx'_def, ENat.toNat_eq_iff_eq_coe, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    IsScalarTower.algebraMap_eq R Rp Sq, ← map_map, Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

-- PRed
theorem ramificationIdx'_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsIntegral R S] [PerfectField (q.under R).ResidueField] :
    q.ramificationIdx' R = 1 ↔ Algebra.IsUnramifiedAt R q := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ramificationIdx'_eq_one q R⟩
  rw [ramificationIdx'_def, ENat.toNat_eq_iff_eq_coe, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at h
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, h⟩

end Ideal

instance {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R] {I : Ideal R} [I.IsPrime]
    [PerfectField (FractionRing R)] :
    PerfectField I.ResidueField := by
  by_cases hI : I = ⊥
  · suffices IsFractionRing R I.ResidueField by
      sorry
    sorry
  · have : Finite (R ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
    have : Finite I.ResidueField := sorry
    infer_instance

instance {I : Ideal ℤ} [I.IsPrime] : PerfectField I.ResidueField :=
  inferInstance

section

variable (G A B C : Type*) [Group G]
    [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B]
    [Algebra A C] [Algebra B C] [FaithfulSMul A C] [FaithfulSMul B C] [IsScalarTower A B C]

theorem NumberField.supr_inertia_eq_top (S G : Type*) [CommRing S] [Module.Finite ℤ S]
    [IsDomain S] [FaithfulSMul ℤ S] [Group G] [MulSemiringAction G S] [IsGaloisGroup G ℤ S] :
    ⨆ m : PrimeSpectrum S, m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have : Finite G := by -- PRed
    let : Algebra (FractionRing ℤ) (FractionRing S) := FractionRing.liftAlgebra ℤ (FractionRing S)
    let : MulSemiringAction G (FractionRing S) :=
        IsFractionRing.mulSemiringAction G ℤ S (FractionRing ℤ) (FractionRing S)
    have : IsGaloisGroup G (FractionRing ℤ) (FractionRing S) :=
      IsGaloisGroup.to_isFractionRing' G ℤ S (FractionRing ℤ) (FractionRing S)
    exact IsGaloisGroup.finite G (FractionRing ℤ) (FractionRing S)
  let H : Subgroup G := ⨆ m : PrimeSpectrum S, m.asIdeal.toAddSubgroup.inertia G
  let R : Subalgebra ℤ S := FixedPoints.subalgebra ℤ S H
  have hH : IsGaloisGroup H R S := inferInstance -- temp
  have : Module.Finite ℤ R := Module.IsNoetherian.finite ℤ R.toSubmodule
  suffices h5 : Algebra.Unramified ℤ R by
    have h4 : Function.Bijective (algebraMap ℤ R) :=
      @bijective_algebraMap_int_of_finite_of_unramified R _ _ h5 _ _
    rw [← IsGaloisGroup.fixingSubgroup_range_algebraMap G ℤ ℤ S ⊤,
      IsScalarTower.algebraMap_eq ℤ R S, RingHom.coe_comp, h4.surjective.range_comp,
      IsGaloisGroup.fixingSubgroup_range_algebraMap G ℤ R S H]
  rw [Algebra.unramified_iff_forall]
  rintro ⟨mF, hmF⟩ -- todo: rename this m's
  simp only
  have : Algebra.IsUnramifiedAt ℤ mF := by
    rw [← Ideal.ramificationIdx'_eq_one_iff]
    have : H.Normal := sorry
    have : IsGaloisGroup (G ⧸ H) ℤ R := sorry
    have : mF.ramificationIdx' ℤ = Nat.card (Ideal.inertia (G ⧸ H) mF) := sorry -- Flat over ℤ
    rw [this, Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall, QuotientGroup.forall_mk]
    intro g hg
    rw [QuotientGroup.eq_one_iff]
    rw [Ideal.inertia, AddSubgroup.inertia] at hg
    simp at hg
    -- Can we go more directly? The quotient `G ⧸ H` is the Galois group of `R/ℤ`,
    -- and the ramification index equals the cardinality of the inertia subgroup (hopefully?),
    -- but the inertia subgroup is trivial (argue directly?)
    have : Module.Finite R S := Module.Finite.of_restrictScalars_finite ℤ R S
    obtain ⟨mK, -, hmK, h⟩ := mF.exists_ideal_over_prime_of_isIntegral (S := S) ⊥ (by simp) -- add liesOver version like the one that exists for maximal
    replace h : mK.LiesOver mF := ⟨h.symm⟩
    have h : mK.inertia G ≤ H :=
      le_iSup (fun m : PrimeSpectrum S ↦ m.asIdeal.inertia G) ⟨mK, hmK⟩
    apply h
    intro x
    specialize hg x
    have : Module.Flat R S := sorry
    have := Ideal.ramificationIdx'_tower (R := ℤ) mF mK -- would be enough to have inequality (is that true in general?)
    have h1 : mK.ramificationIdx' ℤ = Nat.card (Ideal.inertia G mK) := sorry -- doable?
    have h2 : mK.ramificationIdx' R = Nat.card (Ideal.inertia H mK) := sorry -- doable?
    rw [h1, h2] at this
    have h : mK.inertia G ≤ H :=
      le_iSup (fun m : PrimeSpectrum S ↦ m.asIdeal.inertia G) ⟨mK, hmK⟩
    replace h : Nat.card (mK.inertia H) = Nat.card (mK.inertia G) := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h, Subgroup.card_subtype,
        AddSubgroup.subgroupOf_inertia]
    rwa [h, eq_comm, Nat.mul_eq_right] at this
    exact Nat.card_pos.ne'
  exact this

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
