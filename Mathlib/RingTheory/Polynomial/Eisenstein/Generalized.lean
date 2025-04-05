/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open Polynomial Ideal.Quotient

theorem Ideal.IsPrime.mul_not_mem
    {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : R}
    (ha : a ∉ P) (hb : b ∉ P) : a * b ∉ P := fun h ↦
  hb (Or.resolve_left (hP.mem_or_mem h) ha)

/-- The symbolic powers of a prime ideal -/
def Ideal.IsPrime.symbolicPower
    {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) (n : ℕ) : Ideal R where
  carrier := { a : R | ∃ u ∉ P, u * a ∈ P ^ n }
  add_mem' {a b} ha hb := by
    obtain ⟨u, hu, ha⟩ := ha
    obtain ⟨v, hv, hb⟩ := hb
    use u * v, hP.mul_not_mem hu hv
    rw [mul_add]
    apply add_mem
    · rw [mul_assoc, mul_comm v, ← mul_assoc]
      exact IsTwoSided.mul_mem_of_left v ha
    · rw [mul_assoc]
      exact mul_mem_left (P ^ n) u hb
  zero_mem' := ⟨1, (ne_top_iff_one P).mp hP.ne_top, by simp⟩
  smul_mem' c {a} ha := by
    obtain ⟨u, hu, ha⟩ := ha
    use u, hu
    simp only [smul_eq_mul, mul_comm c, ← mul_assoc]
    exact IsTwoSided.mul_mem_of_left c ha

variable {R : Type*} [CommRing R] -- [IsDomain R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  {P : Ideal R} (hP : P.IsPrime)
  {K : Type*} [Field K] [Algebra R K] [Algebra (R ⧸ P) K]
    [IsScalarTower R (R ⧸ P) K] [IsFractionRing (R ⧸ P) K]

variable
-- For the moment, requires q.Monic because Polynomial.divByMonic
    (q : R[X]) (hq_monic : q.Monic) (hq_irr : Irreducible (q.map (algebraMap R K)))

theorem Irreducible.isPow_of_only_factor {q : K[X]} (hq : Irreducible q)
    (f : K[X]) (hfq : ∀ r, Irreducible r → r ∣ f → r ∣ q) (hf0 : f ≠ 0) :
    ∃ m a, f = C a * q ^ m := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ f hf =>
      use 0, f.constantCoeff
      simp only [constantCoeff_apply, pow_zero, mul_one]
      exact eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf)
  | h₃ f g hf hg hind =>
      obtain ⟨m, a , hma⟩ := hind (fun r hr hrf ↦ hfq r hr (Dvd.dvd.mul_left hrf g)) hf
      obtain ⟨u, hfq⟩ := hfq g hg.irreducible (dvd_mul_right g f)
      have u_unit : IsUnit u := by
        apply DvdNotUnit.isUnit_of_irreducible_right ?_ hq
        rw [hfq]
        rw [← dvd_and_not_dvd_iff]
        constructor
        · exact dvd_mul_left u g
        · intro h'
          apply hg.irreducible.not_dvd_one
          obtain ⟨v, hv⟩ := h'
          use v
          apply mul_left_cancel₀ (a := u)
          intro hu
          apply hq.ne_zero
          rw [hfq, hu, mul_zero]
          rw [mul_one, ← mul_assoc, mul_comm u, ← hv]
      letI : Invertible u := u_unit.invertible
      rw [mul_comm, ← invOf_mul_eq_iff_eq_mul_left, mul_comm] at hfq
      have: IsUnit ⅟ u := isUnit_of_invertible ⅟ u
      rw [Polynomial.isUnit_iff] at this
      obtain ⟨b, hb, hu⟩ := this
      use m + 1, a * b
      rw [hma, ← hfq, ← hu, C_mul]
      ring

private theorem map_ne_zero_of_leadingCoeff_not_mem
      {f : R[X]} (hfP : f.leadingCoeff ∉ P) :
      f.map (algebraMap R K) ≠ 0 := fun eq_zero ↦ hfP (by
    simp only [leadingCoeff]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply FaithfulSMul.algebraMap_injective (R ⧸ P) K
    rw [← algebraMap_eq P,
      ← (IsScalarTower.algebraMap_apply R (R ⧸ P) K ), map_zero,
      ← Polynomial.coeff_map, eq_zero, coeff_zero])

theorem exists_C_of_not_mem_mul_eq_C_mul_pow
    (hq_irr : Irreducible (q.map (algebraMap R K)))
    {f : R[X]}
    (hP : P.IsPrime) (hfP : f.leadingCoeff ∉ P)
    (hfq1 : ∀ r, Irreducible r → r ∣ f.map (algebraMap R K) → r ∣ q.map (algebraMap R K)) :
    ∃ a b m r, b ∉ P ∧ map (algebraMap R (R ⧸P)) r = 0 ∧
      C b * f = C a * q ^ m + r := by
  have := hq_irr.isPow_of_only_factor (f.map (algebraMap R K))
    (fun r hr hrdiv ↦ hfq1 _ hr hrdiv)
    (fun eq_zero ↦ by
      apply hfP
      simp only [leadingCoeff]
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply FaithfulSMul.algebraMap_injective (R ⧸ P) K
      rw [← algebraMap_eq P,
        ← (IsScalarTower.algebraMap_apply R (R ⧸ P) K ), map_zero,
        ← Polynomial.coeff_map, eq_zero, coeff_zero])
  obtain ⟨m, a, hma⟩ := this
  obtain ⟨⟨a1, ⟨a2, ha2⟩⟩, ha12⟩ :=
    IsLocalization.surj' (R := R ⧸ P) (S := K) (M := nonZeroDivisors (R ⧸P)) a
  obtain ⟨a1, rfl⟩ := Ideal.Quotient.mk_surjective a1
  obtain ⟨a2, rfl⟩ := Ideal.Quotient.mk_surjective a2
  rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, eq_zero_iff_mem] at ha2
  simp only [← algebraMap_eq P,
    ← (IsScalarTower.algebraMap_apply R (R ⧸ P) K )] at ha12
  use a1, a2, m, C a2 * f - C a1 * q ^ m
  refine ⟨ha2, ?_, by ring⟩
  have : Function.Injective (map (algebraMap (R ⧸ P) K)) := by
    rw [map_injective_iff (algebraMap (R ⧸ P) K)]
    apply FaithfulSMul.algebraMap_injective
  rw [Polynomial.map_sub, sub_eq_zero, ← this.eq_iff]
  simp only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    Polynomial.map_mul, hma, ← mul_assoc, Polynomial.map_pow]
  simp only [Polynomial.map_C, ← C_mul, mul_comm, ha12]

theorem foo {R : Type*} [CommRing R] {I : Ideal R} {f q : R[X]} (hq : q.Monic)
    (hf : ∀ n, f.coeff n ∈ I) (n) :
    (f %ₘ q).coeff n ∈ I := by
  have hf' (f : R[X]) : f.map (mk I) = 0 ↔ ∀ n, f.coeff n ∈ I := by
    simp_rw [← eq_zero_iff_mem, ← coeff_map, ext_iff, coeff_zero]
  revert n
  rw [← hf'] at hf
  rw [← hf', map_modByMonic _ hq, hf, zero_modByMonic]

example [IsDomain R] {f : R[X]} (hfd0 : 0 < degree f)
    (hfP : f.leadingCoeff ∉ P)
    (hfq1 : ∀ r, Irreducible r → r ∣ f.map (algebraMap R K) → r ∣ q.map (algebraMap R K))
    (hfq2 : ∃ n, (f.modByMonic q).coeff n ∉ hP.symbolicPower 2) :
    Irreducible f :=
  have hfd0 : 0 < f.natDegree := WithBot.coe_lt_coe.1 (lt_of_lt_of_le hfd0 degree_le_natDegree)
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfd0
  { not_unit := mt degree_eq_zero_of_isUnit fun h => by simp_all only [lt_irrefl]
    isUnit_or_isUnit' g h h_eq := by
      obtain ⟨a1, a2, m, hg⟩ :=
        exists_C_of_not_mem_mul_eq_C_mul_pow (f := g) q hq_irr hP
        (fun hgP ↦ hfP <| by
          rw [h_eq, leadingCoeff_mul]
          exact P.mul_mem_right _ hgP)
        (fun r hr hrdiv ↦ by
          apply hfq1 r hr
          simp only [h_eq, Polynomial.map_mul]
          exact Dvd.dvd.mul_right hrdiv (map (algebraMap R K) h))
      obtain ⟨a1, a2, m, r, ha2, hr, hg⟩ :=
        exists_C_of_not_mem_mul_eq_C_mul_pow (f := g) q hq_irr hP
        (fun hgP ↦ hfP <| by
          rw [h_eq, leadingCoeff_mul]
          exact P.mul_mem_right _ hgP)
        (fun r hr hrdiv ↦ by
          apply hfq1 r hr
          simp only [h_eq, Polynomial.map_mul]
          exact Dvd.dvd.mul_right hrdiv _)
      have hgP : g.leadingCoeff ∉ P := fun hgP ↦ by
        apply hfP
        rw [h_eq, leadingCoeff_mul]
        exact P.mul_mem_right _ hgP
      by_cases hm : m = 0
      · rw [hm, pow_zero, mul_one] at hg
        left
        suffices g.natDegree = 0 by
          sorry
        by_contra hg'
        apply hgP
        apply Or.resolve_left (hP.mem_or_mem _) ha2
        rw [← leadingCoeff_C a2, ← leadingCoeff_mul, hg, leadingCoeff, coeff_add,
          ← hg, natDegree_C_mul, coeff_C, if_neg hg', zero_add, ← eq_zero_iff_mem,
          ← Polynomial.coeff_map, ← algebraMap_eq P, hr, coeff_zero]
        intro ha2'
        apply ha2
        simp [ha2']
      obtain ⟨b1, b2, n, s, hb2, hs, hh⟩ :=
        exists_C_of_not_mem_mul_eq_C_mul_pow (f := h) q hq_irr hP
        (fun hhP ↦ hfP <| by
          rw [h_eq, leadingCoeff_mul]
          exact P.mul_mem_left _ hhP)
        (fun r hr hrdiv ↦ by
          apply hfq1 r hr
          simp only [h_eq, Polynomial.map_mul]
          exact Dvd.dvd.mul_left hrdiv _)
      have hhP : h.leadingCoeff ∉ P := fun hhP ↦ by
        apply hfP
        rw [h_eq, leadingCoeff_mul]
        exact P.mul_mem_left _ hhP
      by_cases hn : n = 0
      · rw [hn, pow_zero, mul_one] at hh
        right
        suffices h.natDegree = 0 by
          sorry
        by_contra hh'
        apply hhP
        apply Or.resolve_left (hP.mem_or_mem _) hb2
        rw [← leadingCoeff_C b2, ← leadingCoeff_mul, hh, leadingCoeff, coeff_add,
          ← hh, natDegree_C_mul, coeff_C, if_neg hh', zero_add, ← eq_zero_iff_mem,
          ← Polynomial.coeff_map, ← algebraMap_eq P, hs, coeff_zero]
        intro hb2'
        apply hb2
        simp [hb2']
      have h_eq' : C (a2 * b2) * f = (C a1 * q ^ m + r) * (C b1 * q ^n + s) := by
        rw [← hg, ← hh, h_eq, C_mul]
        ring
      have : (C (a2 * b2) * f) %ₘ q = (r * s) %ₘ q := by
        simp only [← Polynomial.smul_eq_C_mul]
        simp only [← Polynomial.modByMonicHom_apply]
        simp only [Polynomial.smul_eq_C_mul, h_eq']
        simp only [add_mul, mul_add, map_add]
        simp only [← add_assoc]
        simp only [modByMonicHom_apply]
        convert zero_add _
        convert zero_add _
        · convert zero_add _
          · rw [modByMonic_eq_zero_iff_dvd hq_monic]
            apply Dvd.dvd.mul_left
            apply Dvd.dvd.mul_left
            exact dvd_pow_self q hn
          · symm
            rw [modByMonic_eq_zero_iff_dvd hq_monic]
            simp only [← mul_assoc]
            apply Dvd.dvd.mul_left
            exact dvd_pow_self q hn
        · symm
          rw [modByMonic_eq_zero_iff_dvd hq_monic]
          apply Dvd.dvd.mul_right; apply Dvd.dvd.mul_left
          exact dvd_pow_self q hm
      exfalso
      obtain ⟨n, hn⟩ := hfq2
      apply hn
      use a2 * b2, hP.mul_not_mem ha2 hb2
      rw [← coeff_C_mul]
      simp only [← smul_eq_C_mul, ← modByMonicHom_apply, ← map_smul]
      rw [Polynomial.smul_eq_C_mul, modByMonicHom_apply, this]
      apply foo hq_monic
      intro n
      rw [coeff_mul]
      rw [← eq_zero_iff_mem, map_sum]
      apply Finset.sum_eq_zero
      intro x hx
      rw [eq_zero_iff_mem, pow_two]
      apply Ideal.mul_mem_mul
      · rw [← eq_zero_iff_mem, ← coeff_map, ← algebraMap_eq P, hr, coeff_zero]
      · rw [← eq_zero_iff_mem, ← coeff_map, ← algebraMap_eq P, hs, coeff_zero] }

