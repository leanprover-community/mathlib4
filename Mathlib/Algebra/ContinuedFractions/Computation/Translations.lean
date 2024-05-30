/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Algebra.ContinuedFractions.ContinuantRecurrence
import Mathlib.Algebra.ContinuedFractions.EvalEquiv

#align_import algebra.continued_fractions.computation.translations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `Algebra.ContinuedFractions.Computation.Basic`. The file consists
of two sections:
1. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
2. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`CF.of`) are connected, i.e. how the values are moved along the
   structures and the termination of one sequence implies the termination of another sequence.

-/

open Int Seq' GCF


namespace CF

open CF (of)

-- Fix a discrete linear ordered floor field and a value `v`.
variable {K : Type*} [LinearOrderedField K] [FloorRing K] (v : K)

#noalign generalized_continued_fraction.int_fract_pair.stream_zero

#noalign generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero

@[simp]
theorem fractParts_dest :
    dest (fractParts v) =
      if fract v = 0 then none else some (fract v, fractParts (fract v)⁻¹) := by
  by_cases hv : fract v = 0 <;> simp [fractParts, hv]

@[simp]
theorem fractParts_int (a : ℤ) : fractParts (a : K) = nil := by
  apply dest_eq_nil
  simp

@[simp]
theorem fractParts_zero : fractParts (0 : K) = nil := by
  apply dest_eq_nil
  simp

@[simp]
theorem head_fractParts :
    head (fractParts v) =
      if fract v = 0 then none else some (fract v) := by
  by_cases hv : fract v = 0 <;> simp [head_eq_dest, hv]

@[simp]
theorem tail_fractParts :
    tail (fractParts v) = fractParts (fract v)⁻¹ := by
  by_cases hv : fract v = 0 <;> simp [tail_eq_dest, hv]

@[simp]
theorem fractParts_fract : fractParts (fract v) = fractParts v := by
  apply dest_injective
  simp

#noalign generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff

#noalign generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff

#noalign generalized_continued_fraction.int_fract_pair.stream_succ_of_some

#noalign generalized_continued_fraction.int_fract_pair.stream_succ_of_int

#noalign generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero

#noalign generalized_continued_fraction.int_fract_pair.stream_succ

section Head

#noalign generalized_continued_fraction.int_fract_pair.seq1_fst_eq_of

#noalign generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
theorem of_h_eq_floor : (of v).h = ⌊v⌋ :=
  rfl
#align generalized_continued_fraction.of_h_eq_floor CF.of_h_eq_floor

end Head

section sequence

/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures (`CF.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one
sequence implies the termination of another sequence.
-/


#noalign generalized_continued_fraction.int_fract_pair.nth_seq1_eq_succ_nth_stream

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/


#noalign generalized_continued_fraction.of_terminated_at_iff_int_fract_pair_seq1_terminated_at

#noalign generalized_continued_fraction.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/

#noalign generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some

#noalign generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream

#noalign generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero

#noalign generalized_continued_fraction.of_s_head_aux

/-- If `a` is an integer, then the coefficient sequence of its continued fraction is empty.
-/
theorem of_s_of_int (a : ℤ) : (of (a : K)).s = nil := by
  apply dest_eq_nil
  simp [of]
#align generalized_continued_fraction.of_s_of_int CF.of_s_of_int

@[simp]
theorem of_int (a : ℤ) : of (a : K) = ⟨a, nil⟩ := by
  ext1 <;> simp [of_s_of_int]

theorem of_s_zero : (of (0 : K)).s = nil := by
  apply dest_eq_nil
  simp [of]

@[simp]
theorem of_zero : of (0 : K) = ⟨0, nil⟩ := by
  ext1 <;> simp [of_s_zero]

@[simp]
theorem of_s_dest :
    dest (of v).s =
      if hv : fract v = 0 then none else
        some (⟨⌊(fract v)⁻¹⌋₊,
          of.proof ⟨fract_nonneg v, fract_lt_one v⟩ hv⟩, (of (fract v)⁻¹).s) := by
  by_cases hv : fract v = 0 <;> simp [of, hv]

/-- This gives the first pair of coefficients of the continued fraction of a non-integer `v`.
-/
@[simp]
theorem of_s_head :
    head (of v).s =
      if hv : fract v = 0 then none else
        some ⟨⌊(fract v)⁻¹⌋₊,
          of.proof ⟨fract_nonneg v, fract_lt_one v⟩ hv⟩ := by
  by_cases hv : fract v = 0 <;> simp [head_eq_dest, hv]
#align generalized_continued_fraction.of_s_head CF.of_s_head

/-- This expresses the tail of the coefficient sequence of the `CF.of`
an element `v` of `K` as the coefficient sequence of that of the inverse of the
fractional part of `v`.
-/
@[simp]
theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s := by
  by_cases hv : fract v = 0 <;> simp [tail_eq_dest, hv]
#align generalized_continued_fraction.of_s_tail CF.of_s_tail

@[simp]
theorem of_fract_s : (of (fract v)).s = (of v).s := by
  apply dest_injective
  simp

/-- Recurrence for the `CF.of` an element `v` of `K` in terms of
that of the inverse of the fractional part of `v`.
-/
@[simp]
theorem of_s_succ (n : ℕ) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n := by
  simp [get?_succ]
#align generalized_continued_fraction.of_s_succ CF.of_s_succ

theorem map_coe_of_s_eq_map_nat_floor_comp_inv_fractParts :
    map ((↑) : ℕ+ → ℕ) (of v).s = map (Nat.floor ∘ Inv.inv) (fractParts v) := by
  apply coinduction2 v
  intro v
  by_cases hv : fract v = 0 <;> simp [hv]
  exists (fract v)⁻¹

theorem of_terminatedAt_iff_fractParts_terminatedAt (n : ℕ) :
    (of v).s.TerminatedAt n ↔ (fractParts v).TerminatedAt n := by
  simpa using congr_arg (fun s : Seq' ℕ => s.TerminatedAt n)
    (map_coe_of_s_eq_map_nat_floor_comp_inv_fractParts v)

variable (K) (n)

/-- If `a` is an integer, then the `convergents` of its continued fraction expansion
are all equal to `a`.
-/
@[simp]
theorem convergents_mk_nil (a : ℤ) : (⟨a, nil⟩ : CF K).convergents n = a := by
  simp [CF.convergents]
#align generalized_continued_fraction.convergents'_of_int CF.convergents_mk_nil

variable {K}

/-- The recurrence relation for the `convergents` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
theorem convergents_succ :
    (of v).convergents (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convergents n := by
  by_cases hv : fract v = 0
  case pos =>
    simp [Int.fract_eq_iff] at hv; rcases hv with ⟨m, rfl⟩
    simp
  case neg =>
    have hn₁ : (of (fract v)⁻¹).convergents n = (of (fract v)⁻¹).convergents n := rfl
    have hn₂ : (of v).convergents (n + 1) = (of v).convergents (n + 1) := rfl
    rw [← Option.some_inj] at hn₁ hn₂ ⊢
    conv_lhs at hn₁ => rw [CF.convergents]
    conv_lhs at hn₂ => rw [CF.convergents]
    rw [CF.convergents, CF.convergents]
    simp [← FCF.eval?_toFGCF, Seq'.take, FGCF.eval?_eq_evalF?,
      FGCF.evalF?, Option.bind_eq_bind, - Part.coe_some, hv] at hn₁ hn₂ ⊢
    rcases hn₁ with ⟨w, hw₁, -⟩
    simp [hw₁, Option.bind_eq_bind, ite_eq_iff] at hn₂ ⊢
    rcases hn₂ with ⟨_, ⟨hv₂, rfl⟩, -⟩
    conv_rhs => rw [← Option.some_inj, ← FCF.eval?_toFGCF, FGCF.eval?_eq_evalF?, eq_comm]
    simp [hv₂, FGCF.evalF?, hw₁]
    symm; apply natCast_floor_eq_intCast_floor; simp
#align generalized_continued_fraction.convergents'_succ CF.convergents_succ

end Values

end sequence

end CF
