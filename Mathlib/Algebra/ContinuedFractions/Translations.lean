/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Basic

#align_import algebra.continued_fractions.translations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`Algebra.ContinuedFractions.Basic`.
-/


section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/

namespace GCF

variable {α : Type*} {g : GCF α} {n : ℕ}

theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := Iff.rfl
#align generalized_continued_fraction.terminated_at_iff_s_terminated_at GCF.terminatedAt_iff_s_terminatedAt

theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := Iff.rfl
#align generalized_continued_fraction.terminated_at_iff_s_none GCF.terminatedAt_iff_s_none

theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partNums, s_nth_eq]
#align generalized_continued_fraction.part_num_none_iff_s_none GCF.partNum_none_iff_s_none

theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  rw [terminatedAt_iff_s_none, partNum_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_num_none GCF.terminatedAt_iff_partNum_none

theorem partDenom_none_iff_s_none : g.partDenoms.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partDenoms, s_nth_eq]
#align generalized_continued_fraction.part_denom_none_iff_s_none GCF.partDenom_none_iff_s_none

theorem terminatedAt_iff_partDenom_none : g.TerminatedAt n ↔ g.partDenoms.get? n = none :=
  by rw [terminatedAt_iff_s_none, partDenom_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_denom_none GCF.terminatedAt_iff_partDenom_none

theorem partNum_eq_s_fst {gp : α × α} (s_nth_eq : g.s.get? n = some gp) :
    g.partNums.get? n = some gp.1 := by simp [partNums, s_nth_eq]
#align generalized_continued_fraction.part_num_eq_s_a GCF.partNum_eq_s_fst

theorem partDenom_eq_s_snd {gp : α × α} (s_nth_eq : g.s.get? n = some gp) :
    g.partDenoms.get? n = some gp.2 := by simp [partDenoms, s_nth_eq]
#align generalized_continued_fraction.part_denom_eq_s_b GCF.partDenom_eq_s_snd

theorem exists_s_fst_of_partNum {a : α} (nth_partNum_eq : g.partNums.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.1 = a := by
  simpa [partNums, Stream'.Seq.map_get?] using nth_partNum_eq
#align generalized_continued_fraction.exists_s_a_of_part_num GCF.exists_s_fst_of_partNum

theorem exists_s_snd_of_partDenom {b : α}
    (nth_partDenom_eq : g.partDenoms.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.2 = b := by
  simpa [partDenoms, Stream'.Seq.map_get?] using nth_partDenom_eq
#align generalized_continued_fraction.exists_s_b_of_part_denom GCF.exists_s_snd_of_partDenom

end GCF

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/

namespace FGCF

variable {K : Type*} (f : FGCF K) (h : K) (l : List (K × K)) (p : K × K) [DivisionRing K]

#noalign generalized_continued_fraction.nth_cont_eq_succ_nth_cont_aux

theorem num_eq_cont_fst : f.numerator = f.continuant.1 :=
  rfl
#align generalized_continued_fraction.num_eq_conts_a FGCF.num_eq_cont_fstₓ

theorem denom_eq_cont_snd : f.denominator = f.continuant.2 :=
  rfl
#align generalized_continued_fraction.denom_eq_conts_b FGCF.denom_eq_cont_sndₓ

#noalign generalized_continued_fraction.convergent_eq_num_div_denom

#noalign generalized_continued_fraction.convergent_eq_conts_a_div_conts_b

#noalign generalized_continued_fraction.exists_conts_a_of_num

#noalign generalized_continued_fraction.exists_conts_b_of_denom

#noalign generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero

#noalign generalized_continued_fraction.first_continuant_aux_eq_h_one

@[simp]
theorem continuant_mk_nil : continuant ⟨h, []⟩ = (h, 1) :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_eq_h_one FGCF.continuant_mk_nilₓ

@[simp]
theorem numerator_mk_nil : numerator ⟨h, []⟩ = h :=
  rfl
#align generalized_continued_fraction.zeroth_numerator_eq_h FGCF.numerator_mk_nilₓ

@[simp]
theorem denominator_mk_nil : denominator ⟨h, []⟩ = 1 :=
  rfl
#align generalized_continued_fraction.zeroth_denominator_eq_one FGCF.denominator_mk_nilₓ

@[simp]
theorem eval?_mk_nil [DecidableEq K] : eval? ⟨h, []⟩ = some h := by
  simp [eval?]
#align generalized_continued_fraction.zeroth_convergent_eq_h FGCF.eval?_mk_nilₓ

#noalign generalized_continued_fraction.second_continuant_aux_eq

@[simp]
theorem continuant_mk_singleton : continuant ⟨h, [p]⟩ = (p.2 * h + p.1, p.2) := by
  simp [continuant]
#align generalized_continued_fraction.first_continuant_eq FGCF.continuant_mk_singletonₓ

@[simp]
theorem numerator_mk_singleton : numerator ⟨h, [p]⟩ = p.2 * h + p.1 := by
  rw [numerator, continuant_mk_singleton]
#align generalized_continued_fraction.first_numerator_eq FGCF.numerator_mk_singletonₓ

@[simp]
theorem denominator_mk_singleton : denominator ⟨h, [p]⟩ = p.2 := by
  rw [denominator, continuant_mk_singleton]
#align generalized_continued_fraction.first_denominator_eq FGCF.denominator_mk_singletonₓ

#noalign generalized_continued_fraction.zeroth_convergent'_aux_eq_zero

@[simp]
theorem evalF?_mk_nil [DecidableEq K] : evalF? ⟨h, []⟩ = some h := by
  simp [evalF?]
#align generalized_continued_fraction.zeroth_convergent'_eq_h FGCF.evalF?_mk_nilₓ

#noalign generalized_continued_fraction.convergents'_aux_succ_none

#noalign generalized_continued_fraction.convergents'_aux_succ_some

end FGCF

end WithDivisionRing
