/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.FieldTheory.SplittingField.Construction

/-! # Results about coefficients of polynomials being integral -/

@[expose] public section

namespace Polynomial

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

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
