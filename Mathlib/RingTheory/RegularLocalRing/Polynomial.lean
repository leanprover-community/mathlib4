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

-/

@[expose] public section

variable (R : Type*) [CommRing R]

open IsLocalRing Polynomial Ideal

lemma Polynomial.localization_at_comap_maximal_isRegularRing_isRegularRing
    [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply (isRegularLocalRing_iff _).mpr
  apply le_antisymm _ (ringKrullDim_le_spanFinrank_maximalIdeal _)
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have Ker : RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) = q := by
    simpa only [residue, ker_mapRingHom, q] using congrArg (Ideal.map C) (Quotient.mkₐ_ker R _)
  have reg := (isRegularLocalRing_iff R).mp ‹_›
  have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  have fg' := (Submodule.FG.finite_generators fg)
  have ht : (maximalIdeal R).height ≤ q.height :=
    le_of_eq (Polynomial.height_map_C (maximalIdeal R)).symm
  by_cases eq0 : p.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = ⊥
  · have eq : p = (maximalIdeal R).map C := le_antisymm
      (by simpa [← Ker, ← Ideal.map_eq_bot_iff_le_ker, q]) qle
    have ht1 : (maximalIdeal R).height ≤ p.height := by simpa [eq]
    have : Ideal.span ((algebraMap R (Localization.AtPrime p)) '' (maximalIdeal R).generators) =
      maximalIdeal (Localization.AtPrime p) := by
      rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p), RingHom.coe_comp,
        Set.image_comp, ← Ideal.map_span, ← Ideal.map_span]
      simp only [Ideal.span, (maximalIdeal R).span_generators, algebraMap_eq, ← eq,
        Localization.AtPrime.map_eq_maximalIdeal]
    simp only [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_comap p.primeCompl,
      IsLocalization.AtPrime.comap_maximalIdeal _ p, ge_iff_le]
    apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
    simp only [maximalIdeal_height_eq_ringKrullDim, ← reg, Nat.cast_le, ← this,
      ← Submodule.FG.generators_ncard fg]
    exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.Finite.image _ fg'))
      (Set.ncard_image_le fg')
  · have lt : q < p := by
      apply lt_of_le_of_ne qle
      by_contra eq
      exact eq0 ((map_eq_bot_iff_le_ker _).mpr (le_of_eq (Ker.trans eq).symm))
    let _ : IsPrincipalIdealRing (IsLocalRing.ResidueField R)[X] := inferInstance
    rcases IsPrincipalIdealRing.principal (Ideal.map (mapRingHom (residue R)) p) with ⟨x, hx⟩
    rcases map_surjective (residue R) residue_surjective x with ⟨y, hy⟩
    have peq : p = Ideal.span (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}) := by
      calc
      p = p ⊔ RingHom.ker (mapRingHom (residue R)) := by simpa [Ker] using qle
      _ = comap (mapRingHom (residue R)) ((Ideal.span {y}).map (mapRingHom (residue R))) := by
        simp [← Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), hx, Ideal.map_span, hy]
      _ = _ := by
        simp only [Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), Set.union_comm, Ideal.span_union,
          ← Ideal.map_span, Ker, algebraMap_eq, q]
        congr
        exact (maximalIdeal R).span_generators.symm
    simp only [← Localization.AtPrime.map_eq_maximalIdeal, peq, Ideal.map_span]
    rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_comap p.primeCompl,
      IsLocalization.AtPrime.comap_maximalIdeal _ p, Ideal.height_eq_primeHeight]
    apply le_trans _ (WithBot.coe_le_coe.mpr (Ideal.primeHeight_add_one_le_of_lt lt))
    rw [← Ideal.height_eq_primeHeight]
    apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
    rw [WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one, ← reg,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    have fin : (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}).Finite :=
      (fg'.image _).union (Set.finite_singleton y)
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _))
    apply le_trans (Set.ncard_image_le fin) (le_trans (Set.ncard_union_le _ _) _)
    rw [Set.ncard_singleton, add_le_add_iff_right]
    exact le_of_le_of_eq (Set.ncard_image_le fg') (Submodule.FG.generators_ncard fg)

theorem Polynomial.isRegularRing_of_isRegularRing [IsRegularRing R] : IsRegularRing R[X] := by
  apply isRegularRing_iff.mpr (fun p hp ↦ ?_)
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime :=  IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.comap_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have := isRegularRing_iff.mp ‹_› q
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_comap q.primeCompl _ (comap C pS),
      ← IsLocalization.map_comap q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      IsLocalization.comap_map_of_isPrime_disjoint pc _ ‹_› disj,
      IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q) q]
    rfl
  have := localization_at_comap_maximal_isRegularRing_isRegularRing (Localization.AtPrime q) pS eq
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
