/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
import Mathlib.RingTheory.CohenMacaulay.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Polynomial Ring Over CM ring is CM

-/

universe u

variable (R : Type u) [CommRing R]
section Polynomial

open RingTheory.Sequence IsLocalRing Polynomial Ideal

lemma Polynomial.localization_at_comap_maximal_isCM_isCM [IsNoetherianRing R]
    [IsCohenMacaulayLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have ker : RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) = q := by
    simpa only [residue, ker_mapRingHom, q] using congrArg (Ideal.map C) (Quotient.mkₐ_ker R _)
  have cm := (isCohenMacaulayLocalRing_def R).mp ‹_›
  have ne := (depth_ne_top (ModuleCat.of R R)).lt_top
  rw [depth_eq_sSup_length_regular] at cm ne
  rcases @ENat.sSup_mem_of_nonempty_of_lt_top _ (by
    use 0, []
    simpa using IsRegular.nil _ _ ) ne with ⟨rs, reg, mem, len⟩
  rw [← len] at cm
  have : IsRegular (Localization.AtPrime p) (rs.map (algebraMap R (Localization.AtPrime p))) := by
    constructor
    · let _ : Module.Flat R (Localization.AtPrime p) := by

        sorry
      exact IsWeaklyRegular.of_flat reg.1
    · simp only [smul_eq_mul, mul_top]
      apply (ne_top_of_le_ne_top (b := maximalIdeal _) IsPrime.ne_top' _).symm
      simp only [span_le, List.mem_map]
      intro r ⟨s, smem, eq⟩
      rw [← eq, IsScalarTower.algebraMap_eq R R[X], RingHom.comp_apply]
      apply Ideal.mem_comap.mp
      rw [IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p, ← Ideal.mem_comap,
        Polynomial.algebraMap_eq, max]
      exact mem s smem
  by_cases eq0 : p.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = ⊥
  · have eq : p = q := le_antisymm (by simpa [← ker, ← Ideal.map_eq_bot_iff_le_ker]) qle
    have ht1 : p.height = (maximalIdeal R).height := sorry

    sorry
  · have prin : (p.map (Polynomial.mapRingHom (IsLocalRing.residue R))).IsPrincipal := inferInstance
    rcases prin with ⟨g, hg⟩
    have : ((C g.leadingCoeff⁻¹) * g).Monic := by
      simp only [Monic, leadingCoeff_mul, leadingCoeff_C]
      apply inv_mul_cancel₀
      apply Polynomial.leadingCoeff_ne_zero.mpr
      by_contra zero
      simp [hg, zero] at eq0
    sorry

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

theorem MvPolynomial.isCM_of_isCM [IsNoetherianRing R] [IsCohenMacaulayRing R] (n : ℕ):
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  induction' n with n ih
  · exact isCohenMacaulayRing_of_ringEquiv (isEmptyRingEquiv R (Fin 0)).symm
  · let _ := Polynomial.isCM_of_isCM (MvPolynomial (Fin n) R)
    exact isCohenMacaulayRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm

end Polynomial
