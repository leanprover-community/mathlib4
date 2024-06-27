/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yaël Dillies
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.TFAE

/-!
# Statement of Fermat's Last Theorem

This file states Fermat's Last Theorem. We provide a statement over a general semiring with
specific exponent, along with the usual statement over the naturals.
-/

open List

/-- Statement of Fermat's Last Theorem over a given semiring with a specific exponent. -/
def FermatLastTheoremWith (α : Type*) [Semiring α] (n : ℕ) : Prop :=
  ∀ a b c : α, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n

/-- Statement of Fermat's Last Theorem over the naturals for a given exponent. -/
def FermatLastTheoremFor (n : ℕ) : Prop := FermatLastTheoremWith ℕ n

/-- Statement of Fermat's Last Theorem: `a ^ n + b ^ n = c ^ n` has no nontrivial natural solution
when `n ≥ 3`. -/
def FermatLastTheorem : Prop := ∀ n ≥ 3, FermatLastTheoremFor n

lemma fermatLastTheoremFor_zero : FermatLastTheoremFor 0 :=
  fun _ _ _ _ _ _ ↦ by norm_num

lemma not_fermatLastTheoremFor_one : ¬ FermatLastTheoremFor 1 :=
  fun h ↦ h 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma not_fermatLastTheoremFor_two : ¬ FermatLastTheoremFor 2 :=
  fun h ↦ h 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

variable {α : Type*} [Semiring α] [NoZeroDivisors α] {m n : ℕ}

lemma FermatLastTheoremWith.mono (hmn : m ∣ n) (hm : FermatLastTheoremWith α m) :
    FermatLastTheoremWith α n := by
  rintro a b c ha hb hc
  obtain ⟨k, rfl⟩ := hmn
  simp_rw [pow_mul']
  refine hm _ _ _ ?_ ?_ ?_ <;> exact pow_ne_zero _ ‹_›

lemma FermatLastTheoremFor.mono (hmn : m ∣ n) (hm : FermatLastTheoremFor m) :
    FermatLastTheoremFor n := by
  exact FermatLastTheoremWith.mono hmn hm

lemma fermatLastTheoremWith_nat_int_rat_tfae (n : ℕ) :
    TFAE [FermatLastTheoremWith ℕ n, FermatLastTheoremWith ℤ n, FermatLastTheoremWith ℚ n] := by
  tfae_have 1 → 2
  · rintro h a b c ha hb hc habc
    obtain hn | hn := n.even_or_odd
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [hn.pow_abs, habc]
    obtain ha | ha := ha.lt_or_lt <;> obtain hb | hb := hb.lt_or_lt <;>
      obtain hc | hc := hc.lt_or_lt
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_neg, neg_pow a, neg_pow b, neg_pow c, ← mul_add, habc, *]
    · exact (by positivity : 0 < c ^ n).not_lt <| habc.symm.trans_lt <| add_neg (hn.pow_neg ha) <|
        hn.pow_neg hb
    · refine h b.natAbs c.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, add_neg_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine h a.natAbs c.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, neg_add_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine h c.natAbs a.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, neg_add_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · refine h c.natAbs b.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, add_neg_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · exact (by positivity : 0 < a ^ n + b ^ n).not_lt <| habc.trans_lt <| hn.pow_neg hc
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, habc, *]
  tfae_have 2 → 3
  · rintro h a b c ha hb hc habc
    rw [← Rat.num_ne_zero] at ha hb hc
    refine h (a.num * b.den * c.den) (a.den * b.num * c.den) (a.den * b.den * c.num)
      (by positivity) (by positivity) (by positivity) ?_
    have : (a.den * b.den * c.den : ℚ) ^ n ≠ 0 := by positivity
    refine Int.cast_injective <| (div_left_inj' this).1 ?_
    push_cast
    simp only [add_div, ← div_pow, mul_div_mul_comm, div_self (by positivity : (a.den : ℚ) ≠ 0),
      div_self (by positivity : (b.den : ℚ) ≠ 0), div_self (by positivity : (c.den : ℚ) ≠ 0),
      one_mul, mul_one, Rat.num_div_den, habc]
  tfae_have 3 → 1
  · rintro h a b c
    exact mod_cast h a b c
  tfae_finish

lemma fermatLastTheoremFor_iff_nat {n : ℕ} : FermatLastTheoremFor n ↔ FermatLastTheoremWith ℕ n :=
  Iff.rfl

lemma fermatLastTheoremFor_iff_int {n : ℕ} : FermatLastTheoremFor n ↔ FermatLastTheoremWith ℤ n :=
  (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 1

lemma fermatLastTheoremFor_iff_rat {n : ℕ} : FermatLastTheoremFor n ↔ FermatLastTheoremWith ℚ n :=
  (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 2

open Finset in
/-- To prove Fermat Last Theorem in any semiring that is a `NormalizedGCDMonoid` one can assume
that the `gcd` of `{a, b, c}` is `1`. -/
lemma fermatLastTheoremWith_of_fermatLastTheoremWith_coprime {n : ℕ} {R : Type*} [CommSemiring R]
    [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    (hn : ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → ({a, b, c} : Finset R).gcd id = 1 →
      a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremWith R n := by
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc habc
  rw [← mul_add, mul_right_inj' (pow_ne_zero n ha.1)] at habc
  refine hn A B C ha.2 hb.2 hc.2 ?_ habc
  rw [← Finset.normalize_gcd, normalize_eq_one]
  obtain ⟨u, hu⟩ := normalize_associated d
  refine ⟨u, mul_left_cancel₀ (mt normalize_eq_zero.mp ha.1) (hu.symm ▸ ?_)⟩
  rw [← Finset.gcd_mul_left, gcd_eq_gcd_image, image_insert, image_insert, image_singleton,
      id_eq, id_eq, id_eq, ← hA, ← hB, ← hC]

lemma dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT {n : ℕ} {p : ℤ} (hp : Prime p)  {a b c : ℤ}
    (hpa : p ∣ a) (hpb : p ∣ b) (HF : a ^ n + b ^ n + c ^ n = 0) : p ∣ c := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at HF
  refine hp.dvd_of_dvd_pow (n := n) (dvd_neg.1 ?_)
  rw [add_eq_zero_iff_eq_neg] at HF
  exact HF.symm ▸ dvd_add (dvd_pow hpa hn) (dvd_pow hpb hn)

lemma isCoprime_of_gcd_eq_one_of_FLT {n : ℕ} {a b c : ℤ} (Hgcd: Finset.gcd {a, b, c} id = 1)
    (HF : a ^ n + b ^ n + c ^ n = 0) : IsCoprime a b := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, Int.reduceAdd, OfNat.ofNat_ne_zero] at HF
  refine isCoprime_of_prime_dvd  ?_ <| (fun p hp hpa hpb ↦ hp.not_dvd_one ?_)
  · rintro ⟨rfl, rfl⟩
    simp only [ne_eq, hn, not_false_eq_true, zero_pow, add_zero, zero_add, pow_eq_zero_iff]
      at HF
    simp only [HF, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.gcd_singleton, id_eq,
      map_zero, zero_ne_one] at Hgcd
  · rw [← Hgcd]
    refine Finset.dvd_gcd_iff.mpr fun x hx ↦ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> simp only [id_eq, hx, hpa, hpb,
      dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT hp hpa hpb HF]
