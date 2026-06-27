/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Polynomial over Regular Ring

In this file we proved that polynomial over regular ring is regular ring.

# Main results

* `Polynomial.isRegularRing_of_isRegularRing` : polynomial over regular ring is regular ring.

* `MvPolynomial.isRegularRing_of_isRegularRing` : multivariate polynomial with finite variates
  over regular ring is regular ring.

-/

@[expose] public section

variable (R : Type*) [CommRing R]

open IsLocalRing Polynomial Ideal

lemma Polynomial.exists_monic_span {k : Type*} [Field k] (I : Ideal k[X]) (ne : I ≠ ⊥) :
    ∃ f, f.Monic ∧ I = Ideal.span {f} := by
  obtain ⟨x, rfl⟩ := IsPrincipalIdealRing.principal I
  have xne : x ≠ 0 := by
    by_contra eq0
    simp [eq0] at ne
  refine ⟨C x.leadingCoeff⁻¹ * x, ?_, ?_⟩
  · simp [Monic, leadingCoeff_ne_zero.mpr xne]
  · apply (Ideal.span_singleton_mul_left_unit _ x).symm
    simpa using xne

lemma Polynomial.exists_monic_span_sup_map_eq (p : Ideal R[X]) [p.IsPrime]
    (ism : (p.comap C).IsMaximal) (ne : p ≠ (p.comap C).map C) :
    ∃ f : R[X], f.Monic ∧ p = (p.comap C).map C ⊔ Ideal.span {f} := by
  let q := p.comap C
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  have ne' : Ideal.map (mapRingHom (Ideal.Quotient.mk q)) p ≠ ⊥ := by
    simp only [ne_eq, map_eq_bot_iff_le_ker, Polynomial.ker_mapRingHom, q, mk_ker]
    exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le ne.symm)
  rcases Polynomial.exists_monic_span _ ne' with ⟨y, mony, hy⟩
  have : y ∈ lifts (Ideal.Quotient.mk q) := map_surjective _ Ideal.Quotient.mk_surjective _
  rcases Polynomial.lifts_and_natDegree_eq_and_monic this mony with ⟨f, hf, deg, monf⟩
  use f, monf
  trans comap (mapRingHom (Ideal.Quotient.mk q)) ((span {f}).map (mapRingHom (Ideal.Quotient.mk q)))
  · rw [Ideal.map_span, coe_mapRingHom, Set.image_singleton, hf, ← hy,
      Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective)]
    simpa [Polynomial.ker_mapRingHom, q] using Ideal.map_comap_le
  · rw [Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective),
      sup_comm, Polynomial.ker_mapRingHom, mk_ker]

lemma Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
    [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have Ker : RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) = q := by
    simpa only [residue, ker_mapRingHom, q] using! congrArg (Ideal.map C) (Quotient.mkₐ_ker R _)
  have reg := (isRegularLocalRing_iff R).mp ‹_›
  have fg' := (maximalIdeal R).fg_of_isNoetherianRing
  have fg := Submodule.FG.finite_generators fg'
  have ht : (maximalIdeal R).height ≤ q.height := le_of_eq (height_map_C (maximalIdeal R)).symm
  by_cases eq : p = q
  · have ht1 : (maximalIdeal R).height ≤ p.height := by simpa [eq]
    have : Ideal.span ((algebraMap R (Localization.AtPrime p)) '' (maximalIdeal R).generators) =
      maximalIdeal (Localization.AtPrime p) := by
      rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p), RingHom.coe_comp,
        Set.image_comp, ← Ideal.map_span, ← Ideal.map_span]
      simp only [Ideal.span, (maximalIdeal R).span_generators, algebraMap_eq, q, ← eq,
        Localization.AtPrime.map_eq_maximalIdeal]
    simp only [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
      IsLocalization.AtPrime.under_maximalIdeal _ p, ge_iff_le]
    apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
    simp only [maximalIdeal_height_eq_ringKrullDim, ← reg, Nat.cast_le, ← this,
      ← Submodule.FG.generators_ncard fg']
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (fg.image _)).trans (Set.ncard_image_le fg)
  · have lt : q < p := lt_of_le_of_ne qle (Ne.symm eq)
    have : (comap C p).IsMaximal := by simpa [max] using maximalIdeal.isMaximal R
    obtain ⟨y, _, hy⟩ := Polynomial.exists_monic_span_sup_map_eq R p this (by simpa [max])
    have peq : p = Ideal.span (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}) := by
      simp only [Set.union_comm, Ideal.span_union, ← Ideal.map_span, algebraMap_eq, sup_comm]
      nth_rw 1 [hy, max, ← (maximalIdeal R).span_generators]
    simp only [← Localization.AtPrime.map_eq_maximalIdeal, peq, Ideal.map_span]
    rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
      IsLocalization.AtPrime.under_maximalIdeal _ p]
    apply le_trans _ (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime lt))
    apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
    rw [WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one, ← reg,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    have fin := (fg.image (algebraMap R R[X])).union (Set.finite_singleton y)
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _))
    apply le_trans (Set.ncard_image_le fin) (le_trans (Set.ncard_union_le _ _) _)
    rw [Set.ncard_singleton, add_le_add_iff_right, ← Submodule.FG.generators_ncard fg']
    exact Set.ncard_image_le fg

theorem Polynomial.isRegularRing_of_isRegularRing [IsRegularRing R] : IsRegularRing R[X] := by
  apply isRegularRing_iff.mpr (fun p hp ↦ ?_)
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime :=  IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have := isRegularRing_iff.mp ‹_› q
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def R[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have := isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal _ pS eq
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

lemma MvPolynomial.isRegularRing_of_isRegularRing [IsRegularRing R] {ι : Type*} [Finite ι] :
    IsRegularRing (MvPolynomial ι R) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H => exact IsRegularRing.of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => exact IsRegularRing.of_ringEquiv (isEmptyRingEquiv R _).symm
  | h_option IH =>
    have := Polynomial.isRegularRing_of_isRegularRing
    exact IsRegularRing.of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv.symm
