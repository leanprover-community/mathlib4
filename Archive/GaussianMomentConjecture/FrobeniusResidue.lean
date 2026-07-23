/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Frobenius residue arithmetic for the GMC(2) lowest-face proof

This module formalizes the characteristic-`p` arithmetic core of `the lowest-balanced-face theorem`.
It deliberately avoids number fields and prime-ideal existence: after reduction
to any residue ring of prime characteristic, it proves the three identities
used by the lowest-balanced-face argument.

* a multinomial coefficient of total mass divisible by `p` vanishes modulo
  `p` unless every exponent is divisible by `p`;
* componentwise dilation by `p` preserves a multinomial coefficient modulo
  `p` (multinomial Lucas in the exact form used in the proof);
* the surviving weighted face sum is the `p`-th power of the original face
  sum, and every strict integral off-face factorial quotient is divisible by
  `p`.

The first statement is proved without formalizing carries: multivariate
Frobenius says the relevant power is an exponent expansion, whose coefficients
outside the `p`-divisible lattice are zero.
-/

open Finset

namespace GMC2.FrobeniusResidue

/-- Frobenius fixes natural-number coefficients and distributes over a finite
weighted sum.  This is the final `Q ↦ Q^p` step of the whole-face residue. -/
theorem weighted_sum_pow_char
    {R ι : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]
    (S : Finset ι) (w : ι → ℕ) (x : ι → R) :
    (∑ i ∈ S, (w i : R) * x i) ^ p =
      ∑ i ∈ S, (w i : R) * x i ^ p := by
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  change (frobenius R p) (w i : R) * x i ^ p = _
  rw [map_natCast]

/-- If the total degree is a multiple of a prime `p` but one exponent is not,
then the corresponding multinomial coefficient is divisible by `p`.

This is the Kummer-isolation conclusion needed by `the lowest-balanced-face theorem`, obtained from
`MvPolynomial.expand` and Frobenius rather than an explicit carry count. -/
theorem prime_dvd_multinomial_of_sum_eq_mul_of_not_dvd
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p m : ℕ) [hp : Fact p.Prime] (r : σ →₀ ℕ)
    (hsum : r.sum (fun _ e => e) = p * m)
    {i : σ} (hi : ¬p ∣ r i) :
    p ∣ r.multinomial := by
  rw [← ZMod.natCast_eq_zero_iff]
  let P : MvPolynomial σ (ZMod p) := ∑ i, MvPolynomial.X i
  let phi : MvPolynomial σ (ZMod p) := P ^ m
  have hexpand : (MvPolynomial.expand p phi).coeff r = 0 :=
    MvPolynomial.coeff_expand_of_not_dvd phi hi
  have hcoeff : MvPolynomial.coeff r (phi ^ p) = 0 := by
    rw [← MvPolynomial.map_frobenius_expand p]
    rw [MvPolynomial.coeff_map, hexpand, map_zero]
  have hpower : phi ^ p = P ^ (p * m) := by
    simp only [phi, mul_comm p m, pow_mul]
  rw [hpower] at hcoeff
  simpa only [P, MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hsum] using hcoeff

/-- Componentwise multiplication of all exponents by `p` preserves the
multinomial coefficient modulo `p`.  This is multinomial Lucas for the exact
dilated channels that survive the Kummer/Frobenius filter. -/
theorem multinomial_dilate_modEq
    {ι : Type*} [DecidableEq ι] (p : ℕ) [Fact p.Prime]
    (S : Finset ι) (r : ι → ℕ) :
    Nat.multinomial S (fun i => p * r i) ≡ Nat.multinomial S r [MOD p] := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Nat.multinomial_empty]
      exact Nat.ModEq.refl 1
  | @insert a S ha ih =>
      rw [Nat.multinomial_insert ha, Nat.multinomial_insert ha]
      have hchoose :
          (p * r a + ∑ i ∈ S, p * r i).choose (p * r a) ≡
            (r a + ∑ i ∈ S, r i).choose (r a) [MOD p] := by
        have hsum : ∑ i ∈ S, p * r i = p * ∑ i ∈ S, r i := by
          rw [Finset.mul_sum]
        rw [hsum, ← Nat.mul_add]
        exact Choose.choose_mul_mul_modEq_choose_nat
      exact hchoose.mul ih

/-- If `A ≥ A₀+1`, then the normalized factorial `(pA)!/(pA₀)!` contains a
factor `p`.  This is the strict off-face vanishing step after the integral
height gap supplied by `GMC2.FrobeniusFace.off_face_integer_gap`. -/
theorem prime_dvd_normalized_factorial_of_gap
    (p A0 A : ℕ) (hp : p.Prime) (hgap : A0 + 1 ≤ A) :
    p ∣ Nat.factorial (p * A) / Nat.factorial (p * A0) := by
  have hA0 : A0 ≤ A := le_trans (Nat.le_succ A0) hgap
  let k := p * (A - A0)
  have hend : p * A0 + k = p * A := by
    dsimp [k]
    rw [← Nat.mul_add, Nat.add_sub_of_le hA0]
  have hquot :
      Nat.factorial (p * A) / Nat.factorial (p * A0) =
        (p * A0 + 1).ascFactorial k := by
    rw [Nat.ascFactorial_eq_div, hend]
  rw [hquot]
  have hk : p ≤ k := by
    have hdiff : 1 ≤ A - A0 := by omega
    dsimp [k]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left p hdiff
  exact (hp.dvd_factorial.mpr hk).trans (Nat.factorial_dvd_ascFactorial _ _)

end GMC2.FrobeniusResidue

/-! The concurrent arithmetic-engine development used the shorter
`GMC2.multinomial_dilate_modEq` name in the historical root module.  Retain
that API as a theorem alias while keeping the residue lemmas in their focused
namespace. -/

namespace GMC2

theorem multinomial_dilate_modEq
    {ι : Type*} [DecidableEq ι] (p : ℕ) [Fact p.Prime]
    (S : Finset ι) (r : ι → ℕ) :
    Nat.multinomial S (fun i => p * r i) ≡ Nat.multinomial S r [MOD p] :=
  GMC2.FrobeniusResidue.multinomial_dilate_modEq p S r

/-- Elementary absorption lemma used by the concurrent no-carry proof. -/
theorem dvd_choose_of_dvd {p : ℕ} (hp : p.Prime) {n k : ℕ}
    (hn : p ∣ n) (hk : ¬ p ∣ k) (hkn : k ≤ n) : p ∣ n.choose k := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr
    (fun h => hk (h ▸ dvd_zero p))
  have hn1 : 1 ≤ n := le_trans hk1 hkn
  have habs : n * (n - 1).choose (k - 1) = n.choose k * k := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    simp only [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hk1] at h
    linarith
  have hdvd : p ∣ n.choose k * k := habs ▸ dvd_mul_of_dvd_left hn _
  exact (hp.dvd_mul.mp hdvd).resolve_right hk

/-- If the total mass is divisible by `p` but one part is not, the
multinomial coefficient is divisible by `p`. -/
theorem multinomial_dvd_of_exists_not_dvd
    {α : Type*} [DecidableEq α] {p : ℕ} (hp : p.Prime)
    (S : Finset α) (r : α → ℕ) (hsum : p ∣ ∑ i ∈ S, r i)
    (hex : ∃ i ∈ S, ¬ p ∣ r i) : p ∣ Nat.multinomial S r := by
  classical
  revert hsum hex
  induction S using Finset.induction_on with
  | empty =>
      intro hsum hex
      obtain ⟨i, hi, hpi⟩ := hex
      exact absurd hi (Finset.notMem_empty i)
  | @insert a S ha ih =>
      intro hsum hex
      rw [Nat.multinomial_insert ha]
      rw [Finset.sum_insert ha] at hsum
      by_cases hra : p ∣ r a
      · have hsumS : p ∣ ∑ i ∈ S, r i := (Nat.dvd_add_right hra).mp hsum
        have hexS : ∃ i ∈ S, ¬ p ∣ r i := by
          obtain ⟨i, hi, hpi⟩ := hex
          rcases Finset.mem_insert.mp hi with rfl | hiS
          · exact absurd hra hpi
          · exact ⟨i, hiS, hpi⟩
        exact dvd_mul_of_dvd_right (ih hsumS hexS) _
      · exact dvd_mul_of_dvd_left
          (dvd_choose_of_dvd hp hsum hra (Nat.le_add_right _ _)) _

/-- Strict base-height growth makes the dilated factorial ratio contain a
factor `p`; compatibility form of the original arithmetic-engine lemma. -/
theorem factorial_dilate_dvd {p : ℕ} (hp : 1 ≤ p) {A0 A : ℕ}
    (h : A0 < A) :
    p * (p * A0).factorial ∣ (p * A).factorial := by
  have h1 : p * (A0 + 1) ≤ p * A := Nat.mul_le_mul le_rfl (by omega)
  have hdvd1 : (p * (A0 + 1)).factorial ∣ (p * A).factorial :=
    Nat.factorial_dvd_factorial h1
  have heq : p * (A0 + 1) = p * A0 + p := by ring
  rw [heq] at hdvd1
  have hpdvd : p ∣ (p * A0 + 1).ascFactorial p :=
    dvd_trans (Nat.dvd_factorial hp le_rfl)
      (Nat.factorial_dvd_ascFactorial _ _)
  calc
    p * (p * A0).factorial ∣
        (p * A0).factorial * (p * A0 + 1).ascFactorial p := by
      rw [mul_comm p]
      exact mul_dvd_mul_left _ hpdvd
    _ = (p * A0 + p).factorial := Nat.factorial_mul_ascFactorial _ _
    _ ∣ (p * A).factorial := hdvd1

/-- Compatibility form of the lowest-balanced-face theorem (15): the complete dilated face sum is
the `p`-th power of its undilated constant-term sum. -/
theorem face_sum_frobenius
    {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {α : Type*} [DecidableEq α] (S : Finset α)
    {ι : Type*} (T : Finset ι) (s : ι → α → ℕ) (h : ι → F) :
    ∑ t ∈ T, (Nat.multinomial S (fun i => p * s t i) : F) * (h t) ^ p =
      (∑ t ∈ T, (Nat.multinomial S (s t) : F) * h t) ^ p := by
  haveI : ExpChar F p := ExpChar.prime Fact.out
  rw [GMC2.FrobeniusResidue.weighted_sum_pow_char]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  exact (CharP.cast_eq_iff_mod_eq F p).mpr
    (multinomial_dilate_modEq p S (s t))

/-- A nonzero face constant term cannot cancel after dilation in a field of
prime characteristic. -/
theorem face_sum_ne_zero
    {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {α : Type*} [DecidableEq α] (S : Finset α)
    {ι : Type*} (T : Finset ι) (s : ι → α → ℕ) (h : ι → F)
    (hQ : (∑ t ∈ T, (Nat.multinomial S (s t) : F) * h t) ≠ 0) :
    ∑ t ∈ T, (Nat.multinomial S (fun i => p * s t i) : F) * (h t) ^ p ≠ 0 := by
  rw [face_sum_frobenius]
  exact pow_ne_zero p hQ

end GMC2

