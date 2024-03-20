/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yaël Dillies
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Int.Basic
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
    · refine' h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [hn.pow_abs, habc]
    obtain ha | ha := ha.lt_or_lt <;> obtain hb | hb := hb.lt_or_lt <;>
      obtain hc | hc := hc.lt_or_lt
    · refine' h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [abs_of_neg, neg_pow a, neg_pow b, neg_pow c, ← mul_add, habc, *]
    · exact (by positivity : 0 < c ^ n).not_lt <| habc.symm.trans_lt <| add_neg (hn.pow_neg ha) <|
        hn.pow_neg hb
    · refine' h b.natAbs c.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, add_neg_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine' h a.natAbs c.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, neg_add_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine' h c.natAbs a.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, neg_add_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · refine' h c.natAbs b.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, habc, add_neg_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · exact (by positivity : 0 < a ^ n + b ^ n).not_lt <| habc.trans_lt <| hn.pow_neg hc
    · refine' h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.coe_nat_inj'.1 _)
      push_cast
      simp only [abs_of_pos, habc, *]
  tfae_have 2 → 3
  · rintro h a b c ha hb hc habc
    rw [← Rat.num_ne_zero] at ha hb hc
    refine' h (a.num * b.den * c.den) (a.den * b.num * c.den) (a.den * b.den * c.num)
      (by positivity) (by positivity) (by positivity) _
    have : (a.den * b.den * c.den : ℚ) ^ n ≠ 0 := by positivity
    refine' Int.cast_injective <| (div_left_inj' this).1 _
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
that the `gcd` of `{a, b, c}` is a unit. -/
lemma fermatLastTheoremWith_of_FermatLastTheoremWith_coprime {n : ℕ} {R : Type*} [CommSemiring R]
    [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    (hn : ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → IsUnit (({a, b, c} : Finset R).gcd id) →
      a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremWith R n := by
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  have hdzero : d ≠ 0 := fun hdzero => by
      simpa [ha] using Finset.gcd_eq_zero_iff.1 hdzero a (by simp [s])
  have hdn : d ^ n ≠ 0 := fun hdn => hdzero (pow_eq_zero hdn)
  refine hn A B C (fun h ↦ ha <| by simpa [h] using hA) (fun h ↦ hb <| by simpa [h] using hB)
    (fun h ↦ hc <| by simpa [h] using hC) ?_ ?_
  · have : d = (GCDMonoid.gcd a (GCDMonoid.gcd b (c * ↑(normUnit c)))) := by
      simp only [d]
      rw [gcd_insert, id_eq]
      simp only [gcd_insert, id_eq, gcd_singleton, normalize_apply]
    simp only [gcd_insert, id_eq, gcd_singleton, normalize_apply]
    apply isUnit_gcd_of_eq_mul_gcd (x := a) (y := GCDMonoid.gcd b (c * (normUnit c)))
    · rw [← this, hA]
    · have H := Finset.normalize_gcd (s := s) (f := id)
      rw [← this, hB, hC, mul_assoc, _root_.gcd_mul_left, H,
        normUnit_mul hdzero fun h ↦ hc <| by simp [h, hC]]
      congr 3
      simp only [Units.val_mul, ne_eq, Units.ne_zero, not_false_eq_true, mul_eq_right₀,
        Units.val_eq_one]
      nth_rewrite 2 [← mul_one (s.gcd id)] at H
      exact Units.ext <| by simpa using mul_left_cancel₀ hdzero H
    · simp [hc]
  · rw [hA, hB, hC, mul_pow, mul_pow, mul_pow, ← mul_add] at habc
    simpa [hdn] using habc

/-- To prove Fermat Last Theorem for `ℤ` one can assume that `a`, `b` and `c` are coprime, in the
sense that the gcd of `{a, b, c}` is `1`. -/
lemma FermatLastTheoremWith_int_of_FermatLastTheoremWith_int_coprime {n : ℕ}
    (hn : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremWith ℤ n := by
  refine fermatLastTheoremWith_of_FermatLastTheoremWith_coprime (R := ℤ)
    (fun a b c ha hb hc H h ↦ hn a b c ha hb hc ?_ h)
  rcases Int.isUnit_iff.1 H with (H | H)
  · exact H
  · simp at H

/-- To prove Fermat Last Theorem one can assume that `a`, `b` and `c` are coprime, in the sense
that the gcd of `{a, b, c}` is `1`. -/
lemma FermatLastTheoremFor_of_FermatLastTheoremFor_coprime {n : ℕ}
    (hn : ∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0 → ({a, b, c} : Finset ℕ).gcd id = 1 →
      a ^ n + b ^ n ≠ c ^ n) :
    FermatLastTheoremFor n :=
  fermatLastTheoremWith_of_FermatLastTheoremWith_coprime (R := ℕ)
    (fun a b c ha hb hc H h ↦ hn a b c ha hb hc (by simpa using H) h)
