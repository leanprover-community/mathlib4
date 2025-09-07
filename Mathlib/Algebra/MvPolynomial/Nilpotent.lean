/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Nilpotents and units in multivariate polynomial rings

We prove that
- `MvPolynomial.isNilpotent_iff`:
  A multivariate polynomial is nilpotent iff all its coefficients are.
- `MvPolynomial.isUnit_iff`:
  A multivariate polynomial is invertible iff its constant term is invertible
  and its other coefficients are nilpotent.
-/

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}

-- Subsumed by `isNilpotent_iff` below.
private theorem isNilpotent_iff_of_fintype [Fintype σ] :
    IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i) := by
  classical
  refine Fintype.induction_empty_option ?_ ?_ ?_ σ P
  · intros α β _ e h₁ P
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective), h₁,
      (Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · intro P
    simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
    rfl
  · intro α _ H P
    obtain ⟨P, rfl⟩ := (optionEquivLeft _ _).symm.surjective P
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff, H, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_coeff, Finsupp.coe_update]

theorem isNilpotent_iff : IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i) := by
  obtain ⟨n, f, hf, P, rfl⟩ := P.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf), MvPolynomial.isNilpotent_iff_of_fintype]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun H i ↦ ?_, fun H i ↦ by simpa using H (i.embDomain f)⟩
  by_cases H : i ∈ Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)

instance [IsReduced R] : IsReduced (MvPolynomial σ R) := by
  simp [isReduced_iff, isNilpotent_iff, MvPolynomial.ext_iff]

theorem isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ ∀ i ≠ 0, IsNilpotent (P.coeff i) := by
  classical
  refine ⟨fun H ↦ ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · intros n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, isNilpotent_iff] at H
    convert ← H (n.equivMapDomain (Equiv.optionSubtypeNe i).symm).some
    refine (optionEquivLeft_coeff_coeff _ _ _ _).trans ?_
    simp [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective]
  · have : IsNilpotent (P - C (P.coeff 0)) := by
      simp +contextual [isNilpotent_iff, apply_ite, eq_comm, h₂]
    simpa using this.isUnit_add_right_of_commute (h₁.map C) (.all _ _)

instance : IsLocalHom (C : _ →+* MvPolynomial σ R) where
  map_nonunit := by classical simp +contextual [isUnit_iff, coeff_C, apply_ite]

instance : IsLocalHom (algebraMap R (MvPolynomial σ R)) :=
  inferInstanceAs (IsLocalHom C)

theorem isUnit_iff_totalDegree_of_isReduced [IsReduced R] :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0 := by
  convert isUnit_iff (P := P)
  rw [totalDegree_eq_zero_iff]
  simp [not_imp_comm (a := _ = (0 : R)), Finsupp.ext_iff]

theorem isUnit_iff_eq_C_of_isReduced [IsReduced R] :
    IsUnit P ↔ ∃ r, IsUnit r ∧ P = C r := by
  rw [isUnit_iff_totalDegree_of_isReduced, totalDegree_eq_zero_iff_eq_C]
  refine ⟨fun H ↦ ⟨_, H⟩, ?_⟩
  rintro ⟨r, hr, rfl⟩
  simpa

end MvPolynomial
