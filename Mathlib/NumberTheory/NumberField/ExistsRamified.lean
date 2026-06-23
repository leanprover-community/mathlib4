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

end

section

-- PRed
theorem Ideal.mem_inertia {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]
    {g : G} {I : Ideal R} : g ∈ I.inertia G ↔ ∀ x, g • x - x ∈ I :=
  AddSubgroup.mem_inertia

-- PRed
open Pointwise
theorem Ideal.inertia_smul {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]
    (g : G) (I : Ideal R) : (g • I).inertia G = (I.inertia G).map (MulAut.conj g) := by
  ext x
  simp_rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, MonoidHom.coe_coe,
    MulAut.conj_symm_apply, Ideal.mem_inertia, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [← (MulAction.toPerm g).forall_congr_right]
  simp [mul_smul, smul_sub]

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

open Ideal IsGaloisGroup Pointwise in
/-- A Galois group over `ℤ` is generated by its inertia subgroups. -/
theorem supr_inertia_primeSpectrum_eq_top (S G : Type*) [CommRing S] [Module.Finite ℤ S]
    [IsDomain S] [FaithfulSMul ℤ S] [Group G] [MulSemiringAction G S] [IsGaloisGroup G ℤ S] :
    ⨆ m : PrimeSpectrum S, m.asIdeal.inertia G = ⊤ := by
  have := IsGaloisGroup.finite G ℤ S
  let f : PrimeSpectrum S → Subgroup G := fun m ↦ m.asIdeal.inertia G
  let H : Subgroup G := ⨆ m : PrimeSpectrum S, f m
  have : H.Normal := by
    refine Subgroup.normal_iff_map_conj_eq.mpr fun g ↦ ?_
    rw [Subgroup.map_iSup]
    exact (MulAction.toPerm g).iSup_congr fun P ↦ P.1.inertia_smul g
  let R : Subalgebra ℤ S := FixedPoints.subalgebra ℤ S H
  let := Ring.toIntAlgebra R
  let := mulSemiringActionQuotient G R S H
  let := mulSemiringActionOfNormal G R S H
  have := IsGaloisGroup.quotient G ℤ R S H
  have := Algebra.IsInvariant.isIntegral R S H
  have : Module.Finite ℤ R := inferInstanceAs (Module.Finite ℤ R.toSubmodule)
  suffices Algebra.Unramified ℤ R by
    rw [← fixingSubgroup_range_algebraMap G ℤ ℤ S ⊤, IsScalarTower.algebraMap_eq ℤ R S,
      RingHom.coe_comp, bijective_algebraMap_int_of_finite_of_unramified.surjective.range_comp,
      fixingSubgroup_range_algebraMap G ℤ R S H]
  refine Algebra.unramified_iff_forall.mpr fun ⟨mR, hmR⟩ ↦ ?_
  obtain ⟨mS, hmS, hmRS⟩ := (inferInstance : (Nonempty (mR.primesOver S)))
  rw [← ramificationIdx'_eq_one_iff, ← ramificationIdxIn_eq_ramificationIdx (mR.under ℤ) mR (G ⧸ H),
    ← card_inertia_eq_ramificationIdxIn (mR.under ℤ) mR (G := G ⧸ H), Subgroup.card_eq_one,
    inertia_quotient H mR mS, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact le_iSup f ⟨mS, hmS⟩

/-- A Galois group over `ℤ` is generated by its inertia subgroups. -/
theorem supr_inertia_maximalSpectrum_eq_top (S G : Type*) [CommRing S] [Module.Finite ℤ S]
    [IsDomain S] [FaithfulSMul ℤ S] [Group G] [MulSemiringAction G S] [IsGaloisGroup G ℤ S] :
    ⨆ m : MaximalSpectrum S, m.asIdeal.inertia G = ⊤ := by
  rw [eq_top_iff, ← supr_inertia_primeSpectrum_eq_top S G, iSup_le_iff]
  intro p
  obtain ⟨m, hm, hpm⟩ := p.1.exists_le_maximal p.2.ne_top
  exact le_iSup_of_le ⟨m, hm⟩ (AddSubgroup.inertia_mono G hpm)

end NumberField
