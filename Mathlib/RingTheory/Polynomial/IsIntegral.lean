/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

/-!

# Results about coefficients of polynomials being integral

## Main results
- `Polynomial.isIntegral_coeff_of_dvd`: If a monic polynomial `p` divides another monic polynomial
  with integral coefficients, then the coefficients of `p` are themselves integral.
- `IsIntegral.coeff_of_isFractionRing`: Let `R` be a domain with fraction ring `K`. If
  `p : K[X]` is integral over `R[X]`, then the coefficients of `p` are integral over `R`.
- We also provide the instance `[IsIntegrallyClosed R] : IsIntegrallyClosed R[X]`.

-/

@[expose] public section

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Polynomial

lemma isIntegral_coeff_prod
    (s : Finset ι) (p : ι → S[X]) (H : ∀ i ∈ s, ∀ j, IsIntegral R ((p i).coeff j)) (j : ℕ) :
    IsIntegral R ((s.prod p).coeff j) := by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has, coeff_mul]
    exact IsIntegral.sum _ fun i hi ↦ .mul (H _ (by simp) _) (IH (fun _ _ ↦ H _ (by aesop)) _)

lemma isIntegral_coeff_of_factors [IsDomain S] (p : S[X])
    (hpmon : IsIntegral R p.leadingCoeff) (hp : p.Splits)
    (hpr : ∀ x ∈ p.roots, IsIntegral R x) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  classical
  rw [hp.eq_prod_roots, Multiset.prod_eq_prod_coe, coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  rintro ⟨a, ⟨i, hi⟩⟩ -
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (i.zero_le.trans_lt hi))
  simp [coeff_X, coeff_C, IsIntegral.sub, apply_ite (IsIntegral R),
    isIntegral_one, isIntegral_zero, hpr x hx]

@[stacks 00H6 "(1)"]
lemma isIntegral_coeff_of_dvd [IsDomain S] (p : R[X]) (q : S[X]) (hp : p.Monic)
    (hq : IsIntegral R q.leadingCoeff)
    (H : q ∣ p.map (algebraMap R S)) (i : ℕ) : IsIntegral R (q.coeff i) := by
  wlog hS : IsField S
  · let L := FractionRing S
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S L)
      (FaithfulSMul.algebraMap_injective _ _)).mp ?_
    rw [IsScalarTower.coe_toAlgHom', ← coeff_map]
    refine this p (q.map (algebraMap _ L)) hp ?_ ?_ _ (Field.toIsField L)
    · rw [leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective _ _)]
      exact .algebraMap hq
    · rw [IsScalarTower.algebraMap_eq R S, ← Polynomial.map_map]
      exact Polynomial.map_dvd _ H
  letI := hS.toField
  let L := (p.map (algebraMap R S)).SplittingField
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S L) (algebraMap S L).injective).mp ?_
  rw [IsScalarTower.coe_toAlgHom', ← coeff_map]
  refine Polynomial.isIntegral_coeff_of_factors _ (by simpa using .algebraMap hq) ?_ ?_ i
  · refine .of_dvd ?_ ((hp.map _).map _).ne_zero (Polynomial.map_dvd _ H)
    exact SplittingField.splits (p.map (algebraMap R S))
  · intro x hx
    exact ⟨p, hp, by simpa using aeval_eq_zero_of_dvd_aeval_eq_zero (a := x) H (by simp_all)⟩

end Polynomial

section

open scoped nonZeroDivisors

open Polynomial

attribute [local instance] Polynomial.algebra

@[stacks 00H0 "(1)"]
lemma IsAlmostIntegral.coeff [IsDomain R] [FaithfulSMul R S]
    {p : S[X]} (hp : IsAlmostIntegral R[X] p) (i : ℕ) :
    IsAlmostIntegral R (p.coeff i) := by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n ↦ ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases h : algebraMap R S p.leadingCoeff * q.leadingCoeff ^ n = 0
    · simp [h]
    have h' : q.leadingCoeff ^ n ≠ 0 := by aesop
    use r.leadingCoeff
    simp only [← leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective R S), hr] at h ⊢
    rw [← leadingCoeff_pow' h'] at h ⊢
    rw [leadingCoeff_mul' h]
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with | h n IH =>
  by_cases hp' : p.natDegree = 0
  · obtain ⟨p, rfl⟩ := natDegree_eq_zero.mp hp'
    simp only [coeff_C]
    split_ifs with h
    · simpa using H hp
    · exact (completeIntegralClosure R S).zero_mem
  by_cases hi : i = p.natDegree
  · simp [hi, H hp]
  have : IsAlmostIntegral R[X] p.eraseLead := by
    rw [← self_sub_monomial_natDegree_leadingCoeff, ← mem_completeIntegralClosure,
      ← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S), ← Polynomial.map_pow]
    refine sub_mem hp (mul_mem ?_ (algebraMap_mem (R := R[X]) _ _))
    obtain ⟨r, hr, hr'⟩ := H hp
    refine ⟨C r, by simpa using hr, fun n ↦ ?_⟩
    obtain ⟨s, hs⟩ := hr' n
    exact ⟨C s, by simp [Algebra.smul_def, hs]⟩
  simpa [hi, eraseLead_coeff_of_ne] using
    IH (p := p.eraseLead) _ (p.eraseLead_natDegree_le.trans_lt (by lia)) this rfl

lemma IsIntegral.coeff_of_exists_smul_mem_lifts
    [FaithfulSMul R S] [IsDomain S]
    {p : S[X]} (hp : IsIntegral R[X] p) (hp' : ∃ r ∈ R⁰, r • p ∈ lifts (algebraMap R S)) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  classical
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  obtain ⟨r, hr, q, hq⟩ := hp'
  let R' := Algebra.adjoin ℤ
    (↑((minpoly R[X] p).coeffs.biUnion coeffs ∪ (insert r q.coeffs)) : Set R)
  have : Algebra.FiniteType ℤ R' := ⟨(Subalgebra.fg_top _).mpr <| Subalgebra.fg_adjoin_finset _⟩
  have := Algebra.FiniteType.isNoetherianRing ℤ R'
  have : IsIntegral R'[X] p := by
    suffices minpoly R[X] p ∈ lifts (mapRingHom (algebraMap R' R)) by
      obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic this (minpoly.monic hp)
      refine ⟨q, hq', ?_⟩
      simpa only [algebraMap_def, IsScalarTower.algebraMap_eq R' R S, ← mapRingHom_comp,
        ← eval₂_map, hq] using minpoly.aeval R[X] p
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦ (lifts_iff_coeff_lifts _).mpr fun m ↦ ?_
    simp only [Subalgebra.setRange_algebraMap, SetLike.mem_coe]
    by_cases h : ((minpoly R[X] p).coeff n).coeff m = 0
    · simp [h]
    refine Algebra.subset_adjoin (Finset.mem_union_left _ ?_)
    exact Finset.mem_biUnion.mpr ⟨_, coeff_mem_coeffs (by aesop), coeff_mem_coeffs h⟩
  refine ((this.isAlmostIntegral_of_exists_smul_mem_range ?_).coeff i).isIntegral.tower_top
  refine ⟨C ⟨r, Algebra.subset_adjoin (Finset.mem_union_right _ (by simp))⟩, ?_, ?_⟩
  · simpa [← SetLike.coe_eq_coe] using hr
  · simp only [algebraMap_def, IsScalarTower.algebraMap_eq R' R S, ← mapRingHom_comp,
      ← RingHom.map_range]
    refine ⟨q, (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_, by simpa [Algebra.smul_def] using hq⟩
    simp only [Subalgebra.setRange_algebraMap, SetLike.mem_coe]
    by_cases h : q.coeff n = 0
    · simp [h]
    · exact Algebra.subset_adjoin (Finset.mem_union_right _ (by simp [coeff_mem_coeffs h]))

@[stacks 00H0 "(2)"]
lemma IsIntegral.coeff_of_isFractionRing
    [IsFractionRing R S] [IsDomain R]
    {p : S[X]} (hp : IsIntegral R[X] p) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  have := IsFractionRing.isDomain R (K := S)
  refine hp.coeff_of_exists_smul_mem_lifts ?_ i
  obtain ⟨r, hr⟩ := IsLocalization.integerNormalization_map_to_map R⁰ p
  exact ⟨r, r.2, ⟨_, hr⟩⟩

@[stacks 030A]
instance {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed R[X] := by
  let K := FractionRing R
  have : IsIntegrallyClosed K[X] := UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn R[X] K[X] from .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K[X]
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective _ (IsFractionRing.injective _ _), ?_⟩
  refine fun {p} hp ↦ (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
  exact IsIntegrallyClosed.isIntegral_iff.mp (hp.coeff_of_isFractionRing _)

end
