/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.GroupWithZero.Basic

#align_import algebra.continued_fractions.translations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`Algebra.ContinuedFractions.Basic`.
-/


namespace GeneralizedContinuedFraction

section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type*} {g : GeneralizedContinuedFraction α} {n : ℕ}

theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl

theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by rfl

theorem part_num_none_iff_s_none : g.partialNumerators.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partialNumerators, s_nth_eq]

theorem terminatedAt_iff_part_num_none : g.TerminatedAt n ↔ g.partialNumerators.get? n = none := by
  rw [terminatedAt_iff_s_none, part_num_none_iff_s_none]

theorem part_denom_none_iff_s_none : g.partialDenominators.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partialDenominators, s_nth_eq]

theorem terminatedAt_iff_part_denom_none : g.TerminatedAt n ↔ g.partialDenominators.get? n = none :=
  by rw [terminatedAt_iff_s_none, part_denom_none_iff_s_none]

theorem part_num_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partialNumerators.get? n = some gp.a := by simp [partialNumerators, s_nth_eq]

theorem part_denom_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partialDenominators.get? n = some gp.b := by simp [partialDenominators, s_nth_eq]

theorem exists_s_a_of_part_num {a : α} (nth_part_num_eq : g.partialNumerators.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.a = a := by
  simpa [partialNumerators, Stream'.Seq.map_get?] using nth_part_num_eq

theorem exists_s_b_of_part_denom {b : α}
    (nth_part_denom_eq : g.partialDenominators.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  simpa [partialDenominators, Stream'.Seq.map_get?] using nth_part_denom_eq

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type*} {g : GeneralizedContinuedFraction K} {n : ℕ} [DivisionRing K]

theorem nth_cont_eq_succ_nth_cont_aux : g.continuants n = g.continuantsAux (n + 1) :=
  rfl

theorem num_eq_conts_a : g.numerators n = (g.continuants n).a :=
  rfl

theorem denom_eq_conts_b : g.denominators n = (g.continuants n).b :=
  rfl

theorem convergent_eq_num_div_denom : g.convergents n = g.numerators n / g.denominators n :=
  rfl

theorem convergent_eq_conts_a_div_conts_b :
    g.convergents n = (g.continuants n).a / (g.continuants n).b :=
  rfl

theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.numerators n = A) :
    ∃ conts, g.continuants n = conts ∧ conts.a = A := by simpa

theorem exists_conts_b_of_denom {B : K} (nth_denom_eq : g.denominators n = B) :
    ∃ conts, g.continuants n = conts ∧ conts.b = B := by simpa

@[simp]
theorem zeroth_continuant_aux_eq_one_zero : g.continuantsAux 0 = ⟨1, 0⟩ :=
  rfl

@[simp]
theorem first_continuant_aux_eq_h_one : g.continuantsAux 1 = ⟨g.h, 1⟩ :=
  rfl

@[simp]
theorem zeroth_continuant_eq_h_one : g.continuants 0 = ⟨g.h, 1⟩ :=
  rfl

@[simp]
theorem zeroth_numerator_eq_h : g.numerators 0 = g.h :=
  rfl

@[simp]
theorem zeroth_denominator_eq_one : g.denominators 0 = 1 :=
  rfl

@[simp]
theorem zeroth_convergent_eq_h : g.convergents 0 = g.h := by
  simp [convergent_eq_num_div_denom, num_eq_conts_a, denom_eq_conts_b, div_one]

theorem second_continuant_aux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.continuantsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [zeroth_s_eq, continuantsAux, nextContinuants, nextDenominator, nextNumerator]

theorem first_continuant_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.continuants 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [nth_cont_eq_succ_nth_cont_aux]
  -- porting note: simp used to work here, but now it can't figure out that 1 + 1 = 2
  convert second_continuant_aux_eq zeroth_s_eq

theorem first_numerator_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.numerators 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_continuant_eq zeroth_s_eq]

theorem first_denominator_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.denominators 1 = gp.b := by simp [denom_eq_conts_b, first_continuant_eq zeroth_s_eq]

@[simp]
theorem zeroth_convergent'_aux_eq_zero {s : Stream'.Seq <| Pair K} :
    convergents'Aux s 0 = (0 : K) :=
  rfl

@[simp]
theorem zeroth_convergent'_eq_h : g.convergents' 0 = g.h := by simp [convergents']

theorem convergents'Aux_succ_none {s : Stream'.Seq (Pair K)} (h : s.head = none) (n : ℕ) :
    convergents'Aux s (n + 1) = 0 := by simp [convergents'Aux, h, convergents'Aux.match_1]

theorem convergents'Aux_succ_some {s : Stream'.Seq (Pair K)} {p : Pair K} (h : s.head = some p)
    (n : ℕ) : convergents'Aux s (n + 1) = p.a / (p.b + convergents'Aux s.tail n) := by
  simp [convergents'Aux, h, convergents'Aux.match_1]

end WithDivisionRing

end GeneralizedContinuedFraction
