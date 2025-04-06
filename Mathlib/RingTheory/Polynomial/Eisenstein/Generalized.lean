/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

-- import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Content

/-! # A generalized Eisenstein criterion

`Polynomial.generalizedEisenstein` :
  Let `R` be an integral domain, `P` a prime ideal of `R` and
  let `K` be the field of fractions o f `R ⧸ P`.
  Let `q : R[X]` be a monic polynomial which is irreducible in `K[X]`.
  Let `f : R[X]` be a monic polynomial of strictly positive degree
  whose image in `K[X]` is a power of `q`.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`.
  Then `f` is irreducible.

The Eisenstein criterion is the particular case where `q := X`.

The case of a polynomial `q := X - a` is interesting,
then the mod `P ^ 2` hypothesis can rephrased as saying
that `f.derivative.eval a ∉ P ^ 2`. (TODO)

We give a (possibly non convincing) application to the irreducibility
of the polynomial `X ^ 4 - 10 * X + 1` in `ℤ[X]`.
One argues modulo 3, with `q := X ^ 2 + 1`.

## Remark

The result can also be generalized to the case where
the leading coefficients of `f` and `q` do not belong to `P`.
(By localization at `P`, make these coefficients invertible.)
There are two obstructions, though :

* Usually, one will only obtain irreducibility in `F[X]`, where `F` is the field
of fractions of `R`. (If `R` is a UFD, this will be close to what is wanted,
but not in general.)

* The mod `P ^ 2` hypothesis will have to be rephrased to a condition
in the second symbolic power of `P`. When `P` is a maximal ideal,
that symbolic power coincides with `P ^ 2`, but not in general.

-/

open Polynomial Ideal.Quotient

theorem Ideal.IsPrime.mul_not_mem
    {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : R}
    (ha : a ∉ P) (hb : b ∉ P) : a * b ∉ P := fun h ↦
  hb (Or.resolve_left (hP.mem_or_mem h) ha)

namespace Polynomial

variable {R : Type*} [CommRing R] -- [IsDomain R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  {P : Ideal R}
  {K : Type*} [Field K] [Algebra R K] [Algebra (R ⧸ P) K]
    [IsScalarTower R (R ⧸ P) K] [IsFractionRing (R ⧸ P) K]
  {q : R[X]}

theorem exists_C_leadingCoeff_mul_pow_of_dvd_pow
    {q : K[X]} (hq : Irreducible q) (hq' : Monic q)
    {f : K[X]} {n : ℕ} (hn : f ∣ q ^ n) :
    ∃ m, f = C f.leadingCoeff * q ^ m := by
  obtain ⟨m, hm, hf⟩ := (dvd_prime_pow hq.prime _).mp hn
  use m
  obtain ⟨u, hu⟩ := hf
  rw [mul_comm, eq_comm, ← Units.inv_mul_eq_iff_eq_mul] at hu
  rw [← hu, leadingCoeff_mul]
  congr
  have : q.leadingCoeff = 1 := hq'
  simp [leadingCoeff_pow, map_mul, map_pow, this]
  obtain ⟨a, ha, ha'⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  rw [← ha', leadingCoeff_C]

theorem exists_eq_C_leadingCoeff_mul_pow_add
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    {f : R[X]} {n : ℕ}
    (map_dvd_pow_q : f.map (algebraMap R K) ∣ q.map (algebraMap R K) ^ n)
    (_ : f.leadingCoeff ∉ P) :
    ∃ m r, f = C f.leadingCoeff * q ^ m + r ∧ map (algebraMap R (R ⧸P)) r = 0 := by
  obtain ⟨m, hm⟩ := exists_C_leadingCoeff_mul_pow_of_dvd_pow hq_irr
     (hq_monic.map (algebraMap R K)) map_dvd_pow_q
  use m, f - C f.leadingCoeff * q ^ m, by ring
  rw [Polynomial.map_sub, sub_eq_zero]
  apply (map_injective_iff (algebraMap (R ⧸ P) K)).mpr (FaithfulSMul.algebraMap_injective _ _)
  simp only  [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw  [hm, Polynomial.map_mul, map_C, Polynomial.map_pow]
  congr
  rw [← leadingCoeff_map_of_leadingCoeff_ne_zero, hm, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_pow, hq_monic.map, one_pow, mul_one]
  rwa [IsScalarTower.algebraMap_apply R (R ⧸ P) K, ne_eq,
    FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq, eq_zero_iff_mem]

theorem generalizedEisenstein [IsDomain R] (hP : P.IsPrime)
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    {f : R[X]} {p : ℕ}
    (hfd0 : 0 < natDegree f) (hf_monic : f.Monic)
    (hfmodP : f.map (algebraMap R K) = q.map (algebraMap R K) ^ p)
    (hfmodP2 : (f.modByMonic q).map (mk (P ^ 2)) ≠ 0) :
    Irreducible f :=
  { not_unit := mt degree_eq_zero_of_isUnit fun h => by
      simp_all only [lt_irrefl, natDegree_pos_iff_degree_pos]
    isUnit_or_isUnit' g h h_eq := by
      classical
      have hgP' : IsUnit g.leadingCoeff := by
        apply isUnit_of_mul_isUnit_left (y  := h.leadingCoeff)
        simp [← leadingCoeff_mul, ← h_eq, hf_monic]
      have hgP : g.leadingCoeff ∉ P :=
        fun hgP ↦ hP.ne_top (Ideal.eq_top_of_isUnit_mem P hgP hgP')
      have hhP' : IsUnit h.leadingCoeff := by
        apply isUnit_of_mul_isUnit_right (x  := g.leadingCoeff)
        simp [← leadingCoeff_mul, ← h_eq, hf_monic]
      have hhP : h.leadingCoeff ∉ P :=
        fun hhP ↦ hP.ne_top (Ideal.eq_top_of_isUnit_mem P hhP hhP')
      obtain ⟨m, r, hg, hr⟩ := exists_eq_C_leadingCoeff_mul_pow_add hq_irr hq_monic
        (by rw [← hfmodP, h_eq, Polynomial.map_mul]; apply dvd_mul_right) hgP
      obtain ⟨n, s, hh, hs⟩ := exists_eq_C_leadingCoeff_mul_pow_add hq_irr hq_monic
        (by rw [← hfmodP, h_eq, Polynomial.map_mul]; apply dvd_mul_left) hhP
      by_cases hm : m = 0
      · rw [hm, pow_zero, mul_one] at hg
        left
        suffices g.natDegree = 0 by
          obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp this
          apply IsUnit.map
          rwa [leadingCoeff_C] at hgP'
        by_contra hg'
        apply hgP
        rw [hg, leadingCoeff, coeff_add, ← hg, coeff_C, if_neg hg', zero_add,
          ← eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq P, ← coeff_map, hr, coeff_zero]
      by_cases hn : n = 0
      · rw [hn, pow_zero, mul_one] at hh
        right
        suffices h.natDegree = 0 by
          obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp this
          apply IsUnit.map
          rwa [leadingCoeff_C] at hhP'
        by_contra hh'
        apply hhP
        rw [hh, leadingCoeff, coeff_add, ← hh, coeff_C, if_neg hh', zero_add,
          ← eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq P, ← coeff_map, hs, coeff_zero]
      have : f %ₘ q = (r * s) %ₘ q := by
        rw [h_eq, hg, hh]
        simp only [add_mul, mul_add, map_add, ← modByMonicHom_apply]
        simp only [← add_assoc, modByMonicHom_apply]
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
      apply hfmodP2
      simp only [ext_iff, ← coeff_map, eq_zero_iff_mem]
      rw [← ext_iff]
      rw [this, map_modByMonic _ hq_monic]
      convert zero_modByMonic _
      ext n
      rw [coeff_map, coeff_mul, map_sum, coeff_zero]
      apply Finset.sum_eq_zero
      intro x hx
      rw [eq_zero_iff_mem, pow_two]
      apply Ideal.mul_mem_mul
      · rw [← eq_zero_iff_mem, ← coeff_map, ← Ideal.Quotient.algebraMap_eq P, hr, coeff_zero]
      · rw [← eq_zero_iff_mem, ← coeff_map, ← Ideal.Quotient.algebraMap_eq P, hs, coeff_zero] }

example : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by
  set P : Ideal ℤ := Ideal.span {3}
  have hP' : P.IsMaximal := by
    apply PrincipalIdealRing.isMaximal_of_irreducible
    refine Prime.irreducible Int.prime_three
  have hP : P.IsPrime := hP'.isPrime
  letI : Field (ℤ ⧸ P) := Ideal.Quotient.field P
  set q : ℤ [X] := X ^ 2 + 1 with hq_eq
  let K := ℤ ⧸ P
  have hq_monic : q.Monic := leadingCoeff_X_pow_add_one (by norm_num)
  have hq_deg : (X ^ 2 + 1 : K[X]).natDegree = 2 := by
    simp only [← C_1, Polynomial.natDegree_X_pow_add_C]
  have hq_irr : Irreducible (q.map (algebraMap ℤ K)) := by
    have : map (algebraMap ℤ K) q = X ^ 2 + 1 := by simp [q]
    rw [this]
    have mod3 : ∀ u : ZMod 3, u ^ 2 + 1 ≠ 0 := by decide
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · apply Multiset.eq_zero_of_forall_not_mem
      intro a
      simp only [mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_one, not_and]
      intro _
      let u := Int.quotientSpanNatEquivZMod 3 a
      have : a ^ 2 + 1 = (Int.quotientSpanNatEquivZMod 3).symm (u ^ 2 + 1) := by simp [u]
      rw [this]
      rw [← ne_eq, RingEquiv.map_ne_zero_iff (Int.quotientSpanNatEquivZMod 3).symm]
      apply mod3
    · rw [hq_deg]
    · rw [hq_deg]; norm_num
  set f : ℤ[X] := X ^ 4 - 10 * X ^ 2 + 1 with hf_eq
  have hdeg_f : f.natDegree = 4 := by
    simp [hf_eq]
    conv_rhs => rw [← natDegree_X_pow (R := ℤ) 4]
    apply natDegree_eq_of_degree_eq
    rw [sub_add] --  degree_X_pow (R := ℤ)]
    apply degree_sub_eq_left_of_degree_lt
    apply lt_of_le_of_lt (degree_sub_le _ _)
    rw [← map_ofNat C, degree_mul, degree_C, degree_X_pow]
    simp; norm_num; norm_num
  have hlC_f : f.Monic := by
    suffices coeff (1 : ℤ[X]) 4 = 0 by
      simp [Monic, leadingCoeff, hdeg_f, f, this]
    rw [← C_1, coeff_C, if_neg (by norm_num)]
  have hfq : f = q ^ 2 - 12 * q + 12 := by ring
  apply generalizedEisenstein hP (K := K) hq_irr hq_monic (p := 2)
    (by rw [hdeg_f]; norm_num) hlC_f
  · simp only [hfq, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, ← map_ofNat C, Polynomial.map_C]
    have : (algebraMap ℤ K) (12) = 0 := by
      rw [IsScalarTower.algebraMap_eq ℤ (ℤ ⧸ P) K, RingHom.comp_apply]
      convert map_zero _
      simp only [Ideal.Quotient.algebraMap_eq P, eq_zero_iff_mem, P, Ideal.mem_span_singleton]
      · norm_num
      · exact Submodule.Quotient.instZeroQuotient P
      · exact AddMonoidHomClass.toZeroHomClass
    rw [this]
    simp
  · suffices f %ₘ q = 12 by
      rw [this]
      rw [← map_ofNat C, Polynomial.map_C, ne_eq, C_eq_zero, eq_zero_iff_mem]
      simp [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [hfq]
    rw [← modByMonicHom_apply, LinearMap.map_add]
    convert zero_add _
    · rw [← LinearMap.mem_ker, mem_ker_modByMonic hq_monic]
      rw [pow_two, ← sub_mul]
      apply dvd_mul_left
    · symm
      simp only [modByMonicHom_apply, Polynomial.modByMonic_eq_self_iff hq_monic, f, P]
      apply Polynomial.degree_lt_degree
      suffices q.natDegree = 2 by
        simp only [this, natDegree_ofNat, f, P, K, q]
        norm_num
      rw [hq_eq]
      simp only [← C_1, Polynomial.natDegree_X_pow_add_C]

end Polynomial

#exit


theorem Ideal.coeff_modByMonic_mem
    {R : Type*} [CommRing R] {I : Ideal R} {f q : R[X]} (hq : q.Monic)
    (hf : ∀ n, f.coeff n ∈ I) (n) :
    (f %ₘ q).coeff n ∈ I := by
  have hf' (f : R[X]) : f.map (mk I) = 0 ↔ ∀ n, f.coeff n ∈ I := by
    simp_rw [← eq_zero_iff_mem, ← coeff_map, ext_iff, coeff_zero]
  revert n
  rw [← hf'] at hf
  rw [← hf', map_modByMonic _ hq, hf, zero_modByMonic]



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

theorem eq_C_mul_pow (hP : P.IsPrime)
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    {f : R[X]} (hfP : f.leadingCoeff ∉ P)
    (hfq1 : ∀ r, Irreducible r → r ∣ f.map (algebraMap R K) → r ∣ q.map (algebraMap R K)) :
    ∃ m r, map (algebraMap R (R ⧸P)) r = 0 ∧ f = C f.leadingCoeff * q ^ m + r := by
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
  use m, f - C f.leadingCoeff * q ^ m, ?_, by ring
  rw [Polynomial.map_sub, sub_eq_zero]
  apply (map_injective_iff (algebraMap (R ⧸ P) K)).mpr (FaithfulSMul.algebraMap_injective _ _)
  simp only  [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw  [hma, Polynomial.map_mul, map_C, Polynomial.map_pow]
  congr
  rw [← leadingCoeff_map_of_leadingCoeff_ne_zero, hma, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_pow, hq_monic.map, one_pow, mul_one]
  rwa [IsScalarTower.algebraMap_apply R (R ⧸ P) K, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff,
    Ideal.Quotient.algebraMap_eq, eq_zero_iff_mem]

theorem exists_C_of_not_mem_mul_eq_C_mul_pow
    (hP : P.IsPrime) (hq_irr : Irreducible (q.map (algebraMap R K)))
    {f : R[X]} (hfP : f.leadingCoeff ∉ P)
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

example [IsDomain R] {f : R[X]} (hfd0 : 0 < degree f)
    (hfP : f.leadingCoeff ∉ P)
    (hfq1 : ∀ r, Irreducible r → r ∣ f.map (algebraMap R K) → r ∣ q.map (algebraMap R K))
    (hfq2 : ∃ n, (f.modByMonic q).coeff n ∉ hP.symbolicPower 2) :
    Irreducible f :=
  have hfd0 : 0 < f.natDegree := WithBot.coe_lt_coe.1 (lt_of_lt_of_le hfd0 degree_le_natDegree)
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfd0
  { not_unit := mt degree_eq_zero_of_isUnit fun h => by simp_all only [lt_irrefl]
    isUnit_or_isUnit' g h h_eq := by
      obtain ⟨m, r, hr, hg⟩ := eq_C_mul_pow q hP hq_irr hq_monic (f := g)
        (fun hgP ↦ hfP <| by
          rw [h_eq, leadingCoeff_mul]
          exact P.mul_mem_right _ hgP)
        (fun r hr hrdiv ↦ by
          apply hfq1 r hr
          simp only [h_eq, Polynomial.map_mul]
          exact Dvd.dvd.mul_right hrdiv (map (algebraMap R K) h))
/-      obtain ⟨a1, a2, m, hg⟩ :=
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
          exact Dvd.dvd.mul_right hrdiv _) -/
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

