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


namespace GenContFract

section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl
#align generalized_continued_fraction.terminated_at_iff_s_terminated_at GenContFract.terminatedAt_iff_s_terminatedAt

theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by rfl
#align generalized_continued_fraction.terminated_at_iff_s_none GenContFract.terminatedAt_iff_s_none

theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partNums, s_nth_eq]
#align generalized_continued_fraction.part_num_none_iff_s_none GenContFract.partNum_none_iff_s_none

theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  rw [terminatedAt_iff_s_none, partNum_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_num_none GenContFract.terminatedAt_iff_partNum_none

theorem partDen_none_iff_s_none : g.partDens.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partDens, s_nth_eq]
#align generalized_continued_fraction.part_denom_none_iff_s_none GenContFract.partDen_none_iff_s_none

theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  rw [terminatedAt_iff_s_none, partDen_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_denom_none GenContFract.terminatedAt_iff_partDen_none

theorem partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partNums.get? n = some gp.a := by simp [partNums, s_nth_eq]
#align generalized_continued_fraction.part_num_eq_s_a GenContFract.partNum_eq_s_a

theorem partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partDens.get? n = some gp.b := by simp [partDens, s_nth_eq]
#align generalized_continued_fraction.part_denom_eq_s_b GenContFract.partDen_eq_s_b

theorem exists_s_a_of_partNum {a : α} (nth_partNum_eq : g.partNums.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.a = a := by
  simpa [partNums, Stream'.Seq.map_get?] using nth_partNum_eq
#align generalized_continued_fraction.exists_s_a_of_part_num GenContFract.exists_s_a_of_partNum

theorem exists_s_b_of_partDen {b : α}
    (nth_partDen_eq : g.partDens.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  simpa [partDens, Stream'.Seq.map_get?] using nth_partDen_eq
#align generalized_continued_fraction.exists_s_b_of_part_denom GenContFract.exists_s_b_of_partDen

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem nth_cont_eq_succ_nth_contAux : g.conts n = g.contsAux (n + 1) :=
  rfl
#align generalized_continued_fraction.nth_cont_eq_succ_nth_cont_aux GenContFract.nth_cont_eq_succ_nth_contAux

theorem num_eq_conts_a : g.nums n = (g.conts n).a :=
  rfl
#align generalized_continued_fraction.num_eq_conts_a GenContFract.num_eq_conts_a

theorem den_eq_conts_b : g.dens n = (g.conts n).b :=
  rfl
#align generalized_continued_fraction.denom_eq_conts_b GenContFract.den_eq_conts_b

theorem conv_eq_num_div_den : g.convs n = g.nums n / g.dens n :=
  rfl
#align generalized_continued_fraction.convergent_eq_num_div_denom GenContFract.conv_eq_num_div_den

theorem conv_eq_conts_a_div_conts_b :
    g.convs n = (g.conts n).a / (g.conts n).b :=
  rfl
#align generalized_continued_fraction.convergent_eq_conts_a_div_conts_b GenContFract.conv_eq_conts_a_div_conts_b

theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.nums n = A) :
    ∃ conts, g.conts n = conts ∧ conts.a = A := by simpa
#align generalized_continued_fraction.exists_conts_a_of_num GenContFract.exists_conts_a_of_num

theorem exists_conts_b_of_den {B : K} (nth_denom_eq : g.dens n = B) :
    ∃ conts, g.conts n = conts ∧ conts.b = B := by simpa
#align generalized_continued_fraction.exists_conts_b_of_denom GenContFract.exists_conts_b_of_den

@[simp]
theorem zeroth_contAux_eq_one_zero : g.contsAux 0 = ⟨1, 0⟩ :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero GenContFract.zeroth_contAux_eq_one_zero

@[simp]
theorem first_contAux_eq_h_one : g.contsAux 1 = ⟨g.h, 1⟩ :=
  rfl
#align generalized_continued_fraction.first_continuant_aux_eq_h_one GenContFract.first_contAux_eq_h_one

@[simp]
theorem zeroth_cont_eq_h_one : g.conts 0 = ⟨g.h, 1⟩ :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_eq_h_one GenContFract.zeroth_cont_eq_h_one

@[simp]
theorem zeroth_num_eq_h : g.nums 0 = g.h :=
  rfl
#align generalized_continued_fraction.zeroth_numerator_eq_h GenContFract.zeroth_num_eq_h

@[simp]
theorem zeroth_den_eq_one : g.dens 0 = 1 :=
  rfl
#align generalized_continued_fraction.zeroth_denominator_eq_one GenContFract.zeroth_den_eq_one

@[simp]
theorem zeroth_conv_eq_h : g.convs 0 = g.h := by
  simp [conv_eq_num_div_den, num_eq_conts_a, den_eq_conts_b, div_one]
#align generalized_continued_fraction.zeroth_convergent_eq_h GenContFract.zeroth_conv_eq_h

theorem second_contAux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [zeroth_s_eq, contsAux, nextConts, nextDen, nextNum]
#align generalized_continued_fraction.second_continuant_aux_eq GenContFract.second_contAux_eq

theorem first_cont_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [nth_cont_eq_succ_nth_contAux]
  -- Porting note (#10959): simp used to work here, but now it can't figure out that 1 + 1 = 2
  convert second_contAux_eq zeroth_s_eq
#align generalized_continued_fraction.first_continuant_eq GenContFract.first_cont_eq

theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_cont_eq zeroth_s_eq]
#align generalized_continued_fraction.first_numerator_eq GenContFract.first_num_eq

theorem first_den_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.dens 1 = gp.b := by simp [den_eq_conts_b, first_cont_eq zeroth_s_eq]
#align generalized_continued_fraction.first_denominator_eq GenContFract.first_den_eq

@[simp]
theorem zeroth_conv'Aux_eq_zero {s : Stream'.Seq <| Pair K} :
    convs'Aux s 0 = (0 : K) :=
  rfl
#align generalized_continued_fraction.zeroth_convergent'_aux_eq_zero GenContFract.zeroth_conv'Aux_eq_zero

@[simp]
theorem zeroth_conv'_eq_h : g.convs' 0 = g.h := by simp [convs']
#align generalized_continued_fraction.zeroth_convergent'_eq_h GenContFract.zeroth_conv'_eq_h

theorem convs'Aux_succ_none {s : Stream'.Seq (Pair K)} (h : s.head = none) (n : ℕ) :
    convs'Aux s (n + 1) = 0 := by simp [convs'Aux, h]
#align generalized_continued_fraction.convergents'_aux_succ_none GenContFract.convs'Aux_succ_none

theorem convs'Aux_succ_some {s : Stream'.Seq (Pair K)} {p : Pair K} (h : s.head = some p)
    (n : ℕ) : convs'Aux s (n + 1) = p.a / (p.b + convs'Aux s.tail n) := by
  simp [convs'Aux, h]
#align generalized_continued_fraction.convergents'_aux_succ_some GenContFract.convs'Aux_succ_some

end WithDivisionRing

end GenContFract
