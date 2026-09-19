/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.CohenMacaulay.Basic
public import Mathlib.RingTheory.Ideal.MonicSpan
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!

# Polynomial Ring Over CM ring is CM

-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

section Polynomial

open RingTheory.Sequence IsLocalRing Polynomial Ideal

lemma Polynomial.localization_at_comap_maximal_isCM_isCM [IsNoetherianRing R]
    [IsCohenMacaulayLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have cm := (isCohenMacaulayLocalRing_def R).mp ‹_›
  have ne := (depth_ne_top (ModuleCat.of R R)).lt_top
  rw [depth_eq_sSup_length_regular] at cm ne ⊢
  rcases @ENat.sSup_mem_of_nonempty_of_lt_top _ (by
    use 0, []
    simpa using IsRegular.nil _ _ ) ne with ⟨rs, reg, mem, len⟩
  rw [← len] at cm
  simp only [← maximalIdeal_height_eq_ringKrullDim, WithBot.coe_inj] at cm
  have mem' : ∀ a ∈ (rs.map (algebraMap R (Localization.AtPrime p))),
    a ∈ maximalIdeal (Localization.AtPrime p) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro r hr
    rw [IsScalarTower.algebraMap_eq R R[X], RingHom.comp_apply]
    apply Ideal.mem_comap.mp
    rw [← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p,
      ← Ideal.mem_comap, Polynomial.algebraMap_eq, max]
    exact mem r hr
  have : Module.Flat R (Localization.AtPrime p) := Module.Flat.trans R R[X] _
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, WithBot.coe_le_coe]
  by_cases eq : p = q
  · have reg : IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p))) := by
      refine ⟨IsWeaklyRegular.of_flat reg.1, ?_⟩
      simp only [smul_eq_mul, mul_top]
      apply (ne_top_of_le_ne_top (b := maximalIdeal _) IsPrime.ne_top' _).symm
      simpa only [span_le] using! mem'
    have ht1 : p.height ≤ (maximalIdeal R).height := by
      rw [eq, Polynomial.height_map_C (maximalIdeal R)]
    apply le_trans ht1 (le_sSup _)
    use (rs.map (algebraMap R (Localization.AtPrime p))), reg
    simpa [cm] using mem'
  · have : (p.comap C).IsMaximal := by simpa [max] using maximalIdeal.isMaximal R
    rcases Polynomial.exists_monic_span_sup_map_eq R p this (by simpa [max]) with ⟨f, monf, hf⟩
    have fmem : f ∈ p := by
      rw [hf]
      exact Ideal.mem_sup_right (Submodule.mem_span_singleton_self f)
    have reg'' : IsWeaklyRegular R[X] (rs.map (algebraMap R R[X])) := IsWeaklyRegular.of_flat reg.1
    have reg' : IsWeaklyRegular R[X] ((rs.map (algebraMap R R[X])) ++ [f]) := by
      refine ⟨fun i hi ↦ ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
        Nat.lt_succ_iff] at hi
      rw [List.take_append_of_le_length hi]
      rcases lt_or_eq_of_le hi with lt|eq
      · simpa only [← List.getElem_append_left' lt [f]] using reg''.1 i lt
      · rw [List.getElem_concat_length eq, List.take_of_length_le (ge_of_eq eq), smul_eq_mul,
          mul_top, ← map_ofList, algebraMap_eq]
        let : Algebra R[X] (R ⧸ ofList rs)[X] := RingHom.toAlgebra
          (Polynomial.mapRingHom (Ideal.Quotient.mk _))
        apply (Equiv.isSMulRegular_congr (r := f) (s := f)
          (e := (Ideal.polynomialQuotientEquivQuotientPolynomial (ofList rs)).toEquiv)
          (fun x ↦ by simp [Algebra.smul_def])).mp
        apply IsSMulRegular.of_right_eq_zero_of_smul
        simpa [Algebra.smul_def, algebraMap_def, Quotient.algebraMap_eq, coe_mapRingHom]
          using (mem_nonZeroDivisors_iff.mp
            (monf.map (Ideal.Quotient.mk (ofList rs))).mem_nonZeroDivisors).1
    have mem'' : ∀ r ∈ (((rs.map (algebraMap R R[X])) ++ [f]).map
      (algebraMap R[X] (Localization.AtPrime p))), r ∈ maximalIdeal (Localization.AtPrime p) := by
      intro r hr
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.mem_append,
        List.mem_map, Function.comp_apply, List.mem_cons, List.not_mem_nil, or_false,
        ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq] at hr
      rcases hr with isrs|isf
      · exact mem' _ (List.mem_map.mpr isrs)
      · simpa only [isf, ← mem_comap, IsLocalization.AtPrime.under_maximalIdeal _ p]
    have reg : IsRegular (Localization.AtPrime p)
      (((rs.map (algebraMap R R[X])) ++ [f]).map (algebraMap R[X] (Localization.AtPrime p))) := by
      refine ⟨IsWeaklyRegular.of_flat reg', ?_⟩
      simp only [smul_eq_mul, mul_top]
      apply (ne_top_of_le_ne_top (b := maximalIdeal _) IsPrime.ne_top' _).symm
      simpa only [span_le] using! mem''
    have ht2 : p.height ≤ (maximalIdeal R).height + 1 := by
      rw [← WithBot.coe_le_coe, WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim,
        WithBot.coe_one, ← ringKrullDim_of_isNoetherianRing]
      exact Ideal.height_le_ringKrullDim_of_ne_top IsPrime.ne_top'
    apply le_trans ht2 (le_sSup _)
    use ((rs.map (algebraMap R R[X])) ++ [f]).map (algebraMap R[X] (Localization.AtPrime p)), reg
    simpa [cm] using mem''

theorem Polynomial.isCM_of_isCM [IsNoetherianRing R] [IsCohenMacaulayRing R] :
    IsCohenMacaulayRing R[X] := by
  apply (isCohenMacaulayRing_def _).mpr (fun p hp ↦ ?_)
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
  have := (isCohenMacaulayRing_def R).mp ‹_› q (comap_isPrime C p)
  have : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def R[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj,
      IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
    rfl
  have := localization_at_comap_maximal_isCM_isCM (Localization.AtPrime q) pS this
  exact isCohenMacaulayLocalRing_of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

lemma MvPolynomial.fin_isCM_of_isCM [IsNoetherianRing R] [IsCohenMacaulayRing R] (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact isCohenMacaulayRing_of_ringEquiv (isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih =>
    have := Polynomial.isCM_of_isCM (MvPolynomial (Fin n) R)
    exact isCohenMacaulayRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm

theorem MvPolynomial.isCM_of_isCM_of_finite [IsNoetherianRing R] [IsCohenMacaulayRing R]
    (ι : Type*) [Finite ι] : IsCohenMacaulayRing (MvPolynomial ι R) := by
  have := MvPolynomial.fin_isCM_of_isCM R (Nat.card ι)
  exact isCohenMacaulayRing_of_ringEquiv (renameEquiv _ (Finite.equivFin ι)).toRingEquiv.symm

end Polynomial
