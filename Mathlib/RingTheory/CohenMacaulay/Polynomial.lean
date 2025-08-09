/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
/-!
# Polynomial Ring Over CM ring is CM

-/

universe u

variable (R : Type u) [CommRing R]

section Polynomial

open RingTheory.Sequence IsLocalRing Polynomial Ideal

lemma Polynomial.exist_monic_mem {F : Type u} [Field F] {I : Ideal F[X]} (ne : I ≠ ⊥) :
    ∃ f ∈ I, f.Monic := by
  obtain ⟨g, gmem, gne⟩ : ∃ g ∈ I, g ≠ 0 := by
    by_contra!
    exact ne ((Submodule.eq_bot_iff I).mpr this)
  use C g.leadingCoeff⁻¹ * g
  refine ⟨mul_mem_left I (C g.leadingCoeff⁻¹) gmem, ?_⟩
  simpa [Monic] using inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr gne)

lemma Polynomial.localization_at_comap_maximal_isCM_isCM [IsNoetherianRing R]
    [IsCohenMacaulayLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have ker : RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) = q := by
    simpa only [residue, ker_mapRingHom, q] using congrArg (Ideal.map C) (Quotient.mkₐ_ker R _)
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
    rw [IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p, ← Ideal.mem_comap,
      Polynomial.algebraMap_eq, max]
    exact mem r hr
  let _ : Module.Free R R[X] :=
    let _ : Module.Free R (AddMonoidAlgebra R ℕ) := Module.Free.finsupp R R ℕ
    Module.Free.of_equiv (Polynomial.toFinsuppIsoLinear R).symm
  let _ : Module.Flat R (Localization.AtPrime p) := Module.Flat.trans R R[X] _
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, WithBot.coe_le_coe]
  by_cases eq0 : p.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = ⊥
  · have reg : IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p))) := by
      refine ⟨IsWeaklyRegular.of_flat reg.1, ?_⟩
      simp only [smul_eq_mul, mul_top]
      apply (ne_top_of_le_ne_top (b := maximalIdeal _) IsPrime.ne_top' _).symm
      simpa only [span_le] using mem'
    have eq : p = q := le_antisymm (by simpa [← ker, ← Ideal.map_eq_bot_iff_le_ker]) qle
    have ht1 : p.height ≤ (maximalIdeal R).height := by
      rw [eq]
      exact le_of_eq (Polynomial.height_map_C (maximalIdeal R))
    apply le_trans ht1 (le_sSup _)
    use (rs.map (algebraMap R (Localization.AtPrime p))), reg
    simpa [cm] using mem'
  · rcases exist_monic_mem eq0 with ⟨g, gmem, mong⟩
    have : g ∈ lifts (IsLocalRing.residue R) := map_surjective _ IsLocalRing.residue_surjective _
    rcases Polynomial.lifts_and_natDegree_eq_and_monic this mong with ⟨f, hf, deg, monf⟩
    have fmem : f ∈ p := by
      simp only [← hf, ← coe_mapRingHom, ← mem_comap] at gmem
      rw [comap_map_of_surjective' _ (map_surjective _ IsLocalRing.residue_surjective),
        sup_of_le_left (by simpa [ker_mapRingHom, ker_residue] using qle)] at gmem
      exact gmem
    have reg'' : IsWeaklyRegular R[X] (rs.map (algebraMap R R[X])) := IsWeaklyRegular.of_flat reg.1
    have reg' : IsWeaklyRegular R[X] ((rs.map (algebraMap R R[X])) ++ [f]) := by
      refine ⟨fun i hi ↦ ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
        Nat.lt_succ] at hi
      rw [List.take_append_of_le_length hi]
      rcases lt_or_eq_of_le hi with lt|eq
      · simpa only [← List.getElem_append_left' lt [f]] using reg''.1 i lt
      · rw [List.getElem_concat_length eq, List.take_of_length_le (ge_of_eq eq), smul_eq_mul,
          mul_top, ← map_ofList, algebraMap_eq]
        let _ : Algebra R[X] (R ⧸ ofList rs)[X] := RingHom.toAlgebra
          (Polynomial.mapRingHom (Ideal.Quotient.mk _))
        apply (Equiv.isSMulRegular_congr (r := f) (s := f)
          (e := (Ideal.polynomialQuotientEquivQuotientPolynomial (ofList rs)).toEquiv)
          (fun x ↦ by simp [Algebra.smul_def])).mp
        apply isSMulRegular_of_smul_eq_zero_imp_eq_zero
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
      · simpa only [isf, ← mem_comap, IsLocalization.AtPrime.comap_maximalIdeal _ p]
    have reg : IsRegular (Localization.AtPrime p)
      (((rs.map (algebraMap R R[X])) ++ [f]).map (algebraMap R[X] (Localization.AtPrime p))) := by
      refine ⟨IsWeaklyRegular.of_flat reg', ?_⟩
      simp only [smul_eq_mul, mul_top]
      apply (ne_top_of_le_ne_top (b := maximalIdeal _) IsPrime.ne_top' _).symm
      simpa only [span_le] using mem''
    have ht2 : p.height ≤ (maximalIdeal R).height + 1 := by
      rw [← WithBot.coe_le_coe, WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim,
        height_eq_primeHeight, WithBot.coe_one, ← ringKrullDim_of_isNoetherianRing]
      exact primeHeight_le_ringKrullDim
    apply le_trans ht2 (le_sSup _)
    use ((rs.map (algebraMap R R[X])) ++ [f]).map (algebraMap R[X] (Localization.AtPrime p)), reg
    simpa [cm] using mem''

theorem Polynomial.isCM_of_isCM [IsNoetherianRing R] [IsCohenMacaulayRing R] :
    IsCohenMacaulayRing R[X] := by
  apply (isCohenMacaulayRing_def _).mpr (fun p hp ↦ ?_)
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let _ : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have _ : IsLocalization pc S := {
    map_units' x := by
      rcases x.2 with ⟨y, mem, eq⟩
      apply isUnit_of_mul_eq_one _ (C (Localization.mk 1 ⟨y, mem⟩))
      simp [← eq, S, ← map_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    surj' z := by
      induction' z using Polynomial.induction_on' with f g hf hg n a
      · rcases hf with ⟨⟨x1, y1⟩, h1⟩
        rcases hg with ⟨⟨x2, y2⟩, h2⟩
        use (x2 * y1.1 + x1 * y2.1, y1 * y2)
        simp only [Submonoid.coe_mul, map_mul, add_mul, map_add]
        nth_rw 4 [mul_comm]
        simp [← mul_assoc, h1, h2, add_comm]
      · rcases Localization.mkHom_surjective a with ⟨⟨x, y⟩, h⟩
        use ((monomial n) x, ⟨C y.1, by simp [pc]⟩)
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
      use ⟨C s.1, by simp [pc]⟩
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
  let _ := (isCohenMacaulayRing_def R).mp ‹_› q (comap_isPrime C p)
  have : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_comap q.primeCompl _ (comap C pS),
      ← IsLocalization.map_comap q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      IsLocalization.comap_map_of_isPrime_disjoint pc _ _ ‹_› disj,
      IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q) q]
    rfl
  let _ := localization_at_comap_maximal_isCM_isCM (Localization.AtPrime q) pS this
  exact isCohenMacaulayLocalRing_of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

theorem MvPolynomial.isCM_of_isCM [IsNoetherianRing R] [IsCohenMacaulayRing R] (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  induction' n with n ih
  · exact isCohenMacaulayRing_of_ringEquiv (isEmptyRingEquiv R (Fin 0)).symm
  · let _ := Polynomial.isCM_of_isCM (MvPolynomial (Fin n) R)
    exact isCohenMacaulayRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm

end Polynomial
