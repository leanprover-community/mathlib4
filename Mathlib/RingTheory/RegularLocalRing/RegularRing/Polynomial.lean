/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.RegularRing.Basic
/-!

# Polynomial over Regular Ring

-/

variable (R : Type*) [CommRing R]

open IsLocalRing Polynomial Ideal

open Set in
lemma Polynomial.localization_at_comap_maximal_isRegularRing_isRegularRing
    [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply (isRegularLocalRing_def _).mpr
  apply le_antisymm _ (ringKrullDim_le_spanFinrank_maximalIdeal _)
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have Ker : RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) = q := by
    simpa only [residue, ker_mapRingHom, q] using congrArg (Ideal.map C) (Quotient.mkₐ_ker R _)
  have reg := (isRegularLocalRing_def R).mp ‹_›
  have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  have fg' := (Submodule.FG.finite_generators fg)
  have ht : (maximalIdeal R).height ≤ q.height := by
    --exact le_of_eq (Polynomial.height_map_C (maximalIdeal R)).symm
    sorry
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
  · let _ : q.IsPrime := Ideal.isPrime_map_C_of_isPrime (IsMaximal.isPrime' (maximalIdeal R))
    have lt : q < p := by
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
    apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_right ht 1))
    rw [WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one, ← reg,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    have fin : (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}).Finite :=
      Finite.union (Finite.image _ fg') (finite_singleton y)
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finite.image _ fin))
    apply le_trans (Set.ncard_image_le fin) (le_trans (Set.ncard_union_le _ _) _)
    rw [ncard_singleton, add_le_add_iff_right]
    exact le_of_le_of_eq (Set.ncard_image_le fg') (Submodule.FG.generators_ncard fg)

theorem Polynomial.isRegularRing_of_isRegularRing [IsRegularRing R] :
    IsRegularRing R[X] := by
  apply (isRegularRing_iff _).mpr (fun p hp ↦ ?_)
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let _ : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have _ : IsLocalization pc S := {
    map_units x := by
      rcases x.2 with ⟨y, mem, eq⟩
      apply isUnit_of_mul_eq_one _ (C (Localization.mk 1 ⟨y, mem⟩))
      simp [← eq, S, ← map_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    surj z := by
      induction z using Polynomial.induction_on'
      · rename_i _ _ f g hf hg
        rcases hf with ⟨⟨x1, y1⟩, h1⟩
        rcases hg with ⟨⟨x2, y2⟩, h2⟩
        use (x2 * y1.1 + x1 * y2.1, y1 * y2)
        simp only [Submonoid.coe_mul, map_mul, add_mul, map_add]
        nth_rw 4 [mul_comm]
        simp [← mul_assoc, h1, h2, add_comm]
      · rename_i _ _ n a
        rcases Localization.mkHom_surjective a with ⟨⟨x, y⟩, h⟩
        have : y.1 ∉ q := y.2
        use ((monomial n) x, ⟨C y.1, by simpa [pc]⟩)
        simp only [← h, Localization.mkHom_apply, algebraMap_def, coe_mapRingHom, map_C, ←
          Localization.mk_one_eq_algebraMap, monomial_mul_C, map_monomial, S, Localization.mk_mul]
        congr 1
        apply Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
        simp [mul_comm]
    exists_of_eq {x y} eq := by
      have eq' (n : ℕ) : (algebraMap R (Localization.AtPrime q)) (Polynomial.coeff x n) =
        (algebraMap R (Localization.AtPrime q)) (Polynomial.coeff y n) := by
        simp only [algebraMap_def, coe_mapRingHom, S] at eq
        have : coeff (map (algebraMap R (Localization.AtPrime q)) x) n =
          coeff (map (algebraMap R (Localization.AtPrime q)) y) n := by rw [eq]
        simpa
      let g : ℕ → q.primeCompl := fun n ↦ Classical.choose (IsLocalization.exists_of_eq (eq' n))
      have g_spec (n : ℕ) := Classical.choose_spec
        (IsLocalization.exists_of_eq (M := q.primeCompl) (eq' n))
      let s := ∏ n ∈ x.1.1 ∪ y.1.1, g n
      have : s.1 ∉ q := s.2
      use ⟨C s.1, by simpa [pc]⟩
      ext n
      simp only [coeff_C_mul, s]
      by_cases mem : n ∈ x.1.1 ∪ y.1.1
      · rcases Finset.dvd_prod_of_mem g mem with ⟨t, ht⟩
        simp only [ht, Submonoid.coe_mul, mul_comm _ t.1, mul_assoc]
        rw [g_spec n]
      · simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq, not_or, not_not] at mem
        simp [← Polynomial.toFinsupp_apply, mem] }
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime :=  IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.comap_map_of_isPrime_disjoint pc _ _ ‹_› disj).symm
  let _ := (isRegularRing_iff R).mp ‹_› q (comap_isPrime C p)
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_comap q.primeCompl _ (comap C pS),
      ← IsLocalization.map_comap q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      IsLocalization.comap_map_of_isPrime_disjoint pc _ _ ‹_› disj,
      IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q) q]
    rfl
  let _ := localization_at_comap_maximal_isRegularRing_isRegularRing (Localization.AtPrime q) pS eq
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

lemma MvPolynomial.isRegularRing_of_isRegularRing [IsRegularRing R] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) R) := by
  induction n
  · exact isRegularRing_of_ringEquiv (isEmptyRingEquiv R (Fin 0)).symm
  · rename_i n ih
    let _ := Polynomial.isRegularRing_of_isRegularRing (MvPolynomial (Fin n) R)
    exact isRegularRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm
