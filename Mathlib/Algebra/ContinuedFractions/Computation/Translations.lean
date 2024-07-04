/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Translations

#align_import algebra.continued_fractions.computation.translations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `Algebra.ContinuedFractions.Computation.Basic`. The file consists
of three sections:
1. Recurrences and inversion lemmas for `IntFractPair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`IntFractPair.stream`, `IntFractPair.seq1`, and
   `GeneralizedContinuedFraction.of`) are connected, i.e. how the values are moved along the
   structures and the termination of one sequence implies the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `get?_of_eq_some_of_succ_get?_intFractPair_stream` and
  `get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/


namespace GeneralizedContinuedFraction

open GeneralizedContinuedFraction (of)

-- Fix a discrete linear ordered floor field and a value `v`.
variable {K : Type*} [LinearOrderedField K] [FloorRing K] {v : K}

namespace IntFractPair

/-!
### Recurrences and Inversion Lemmas for `IntFractPair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/


theorem stream_zero (v : K) : IntFractPair.stream v 0 = some (IntFractPair.of v) :=
  rfl
#align generalized_continued_fraction.int_fract_pair.stream_zero GeneralizedContinuedFraction.IntFractPair.stream_zero

variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none := by
  cases' ifp_n with _ fr
  change fr = 0 at nth_fr_eq_zero
  simp [IntFractPair.stream, stream_nth_eq, nth_fr_eq_zero]
#align generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero GeneralizedContinuedFraction.IntFractPair.stream_eq_none_of_fr_eq_zero

/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_none_iff

/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
theorem succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} :
    IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : IntFractPair K,
        IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simp [IntFractPair.stream, ite_eq_iff, Option.bind_eq_some]
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_some_iff

/-- An easier to use version of one direction of
`GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_some_iff`.
-/
theorem stream_succ_of_some {p : IntFractPair K} (h : IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : IntFractPair.stream v (n + 1) = some (IntFractPair.of p.fr⁻¹) :=
  succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩
#align generalized_continued_fraction.int_fract_pair.stream_succ_of_some GeneralizedContinuedFraction.IntFractPair.stream_succ_of_some

/-- The stream of `IntFractPair`s of an integer stops after the first term.
-/
theorem stream_succ_of_int (a : ℤ) (n : ℕ) : IntFractPair.stream (a : K) (n + 1) = none := by
  induction' n with n ih
  · refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  · exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)
#align generalized_continued_fraction.int_fract_pair.stream_succ_of_int GeneralizedContinuedFraction.IntFractPair.stream_succ_of_int

theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero
#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero GeneralizedContinuedFraction.IntFractPair.exists_succ_nth_stream_of_fr_zero

/-- A recurrence relation that expresses the `(n+1)`th term of the stream of `IntFractPair`s
of `v` for non-integer `v` in terms of the `n`th term of the stream associated to
the inverse of the fractional part of `v`.
-/
theorem stream_succ (h : Int.fract v ≠ 0) (n : ℕ) :
    IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻¹ n := by
  induction' n with n ih
  · have H : (IntFractPair.of v).fr = Int.fract v := rfl
    rw [stream_zero, stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h), H]
  · rcases eq_or_ne (IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | hsome
    · rw [hnone] at ih
      rw [succ_nth_stream_eq_none_iff.mpr (Or.inl hnone),
        succ_nth_stream_eq_none_iff.mpr (Or.inl ih)]
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hsome
      rw [hp] at ih
      rcases eq_or_ne p.fr 0 with hz | hnz
      · rw [stream_eq_none_of_fr_eq_zero hp hz, stream_eq_none_of_fr_eq_zero ih hz]
      · rw [stream_succ_of_some hp hnz, stream_succ_of_some ih hnz]
#align generalized_continued_fraction.int_fract_pair.stream_succ GeneralizedContinuedFraction.IntFractPair.stream_succ

end IntFractPair

section Head

/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/


/-- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp]
theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v :=
  rfl
#align generalized_continued_fraction.int_fract_pair.seq1_fst_eq_of GeneralizedContinuedFraction.IntFractPair.seq1_fst_eq_of

theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b := by
  cases aux_seq_eq : IntFractPair.seq1 v
  simp [of, aux_seq_eq]
#align generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b GeneralizedContinuedFraction.of_h_eq_intFractPair_seq1_fst_b

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
theorem of_h_eq_floor : (of v).h = ⌊v⌋ := by
  simp [of_h_eq_intFractPair_seq1_fst_b, IntFractPair.of]
#align generalized_continued_fraction.of_h_eq_floor GeneralizedContinuedFraction.of_h_eq_floor

end Head

section sequence

/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`IntFractPair.stream`, `IntFractPair.seq1`, and `GeneralizedContinuedFraction.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one
sequence implies the termination of another sequence.
-/


variable {n : ℕ}

theorem IntFractPair.get?_seq1_eq_succ_get?_stream :
    (IntFractPair.seq1 v).snd.get? n = (IntFractPair.stream v) (n + 1) :=
  rfl
#align generalized_continued_fraction.int_fract_pair.nth_seq1_eq_succ_nth_stream GeneralizedContinuedFraction.IntFractPair.get?_seq1_eq_succ_get?_stream

section Termination

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/


theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt :
    (of v).TerminatedAt n ↔ (IntFractPair.seq1 v).snd.TerminatedAt n :=
  Option.map_eq_none
#align generalized_continued_fraction.of_terminated_at_iff_int_fract_pair_seq1_terminated_at GeneralizedContinuedFraction.of_terminatedAt_iff_intFractPair_seq1_terminatedAt

theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [of_terminatedAt_iff_intFractPair_seq1_terminatedAt, Stream'.Seq.TerminatedAt,
    IntFractPair.get?_seq1_eq_succ_get?_stream]
#align generalized_continued_fraction.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none GeneralizedContinuedFraction.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none

end Termination

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/


theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.get? n = some gp_n) :
    ∃ ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b := by
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa [Stream'.Seq.get?_tail, Stream'.Seq.map_get?] using s_nth_eq
  cases gp_n_eq
  simp_all only [Option.some.injEq, exists_eq_left']
#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some GeneralizedContinuedFraction.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some

/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
theorem get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.get? n = some ⟨1, ifp_succ_n.b⟩ := by
  unfold of IntFractPair.seq1
  simp [Stream'.Seq.map_tail, Stream'.Seq.get?_tail, Stream'.Seq.map_get?, stream_succ_nth_eq]
#align generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream GeneralizedContinuedFraction.get?_of_eq_some_of_succ_get?_intFractPair_stream

/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
theorem get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
    (of v).s.get? n = some ⟨1, (IntFractPair.of ifp_n.fr⁻¹).b⟩ :=
  have : IntFractPair.stream v (n + 1) = some (IntFractPair.of ifp_n.fr⁻¹) := by
    cases ifp_n
    simp only [IntFractPair.stream, Nat.add_eq, add_zero, stream_nth_eq, Option.some_bind,
      ite_eq_right_iff]
    intro; contradiction
  get?_of_eq_some_of_succ_get?_intFractPair_stream this
#align generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero GeneralizedContinuedFraction.get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero

open Int IntFractPair

theorem of_s_head_aux (v : K) : (of v).s.get? 0 = (IntFractPair.stream v 1).bind (some ∘ fun p =>
    { a := 1
      b := p.b }) := by
  rw [of, IntFractPair.seq1]
  simp only [of, Stream'.Seq.map_tail, Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.head,
    Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ, Stream'.get, Option.map]
  split <;> simp_all only [Option.some_bind, Option.none_bind, Function.comp_apply]
#align generalized_continued_fraction.of_s_head_aux GeneralizedContinuedFraction.of_s_head_aux

/-- This gives the first pair of coefficients of the continued fraction of a non-integer `v`.
-/
theorem of_s_head (h : fract v ≠ 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩ := by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux, stream_succ_of_some (stream_zero v) h, Option.bind]
  rfl
#align generalized_continued_fraction.of_s_head GeneralizedContinuedFraction.of_s_head

variable (K)

/-- If `a` is an integer, then the coefficient sequence of its continued fraction is empty.
-/
theorem of_s_of_int (a : ℤ) : (of (a : K)).s = Stream'.Seq.nil :=
  haveI h : ∀ n, (of (a : K)).s.get? n = none := by
    intro n
    induction' n with n ih
    · rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    · exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm
#align generalized_continued_fraction.of_s_of_int GeneralizedContinuedFraction.of_s_of_int

variable {K} (v)

/-- Recurrence for the `GeneralizedContinuedFraction.of` an element `v` of `K` in terms of
that of the inverse of the fractional part of `v`.
-/
theorem of_s_succ (n : ℕ) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast, inv_zero, of_s_of_int, ← cast_zero, of_s_of_int,
      Stream'.Seq.get?_nil, Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).s.get? n) none with h₁ | h₁
  · rwa [h₁, ← terminatedAt_iff_s_none,
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, stream_succ h, ←
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, terminatedAt_iff_s_none]
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h₁
    obtain ⟨p', hp'₁, _⟩ := exists_succ_get?_stream_of_gcf_of_get?_eq_some hp
    have Hp := get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁
    rw [← stream_succ h] at hp'₁
    rw [Hp, get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁]
#align generalized_continued_fraction.of_s_succ GeneralizedContinuedFraction.of_s_succ

/-- This expresses the tail of the coefficient sequence of the `GeneralizedContinuedFraction.of`
an element `v` of `K` as the coefficient sequence of that of the inverse of the
fractional part of `v`.
-/
theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s :=
  Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ of_s_succ v n
#align generalized_continued_fraction.of_s_tail GeneralizedContinuedFraction.of_s_tail

variable (K) (n)

/-- If `a` is an integer, then the `convergents'` of its continued fraction expansion
are all equal to `a`.
-/
theorem convergents'_of_int (a : ℤ) : (of (a : K)).convergents' n = a := by
  induction' n with n
  · simp only [zeroth_convergent'_eq_h, of_h_eq_floor, floor_intCast, Nat.zero_eq]
  · rw [convergents', of_h_eq_floor, floor_intCast, add_right_eq_self]
    exact convergents'Aux_succ_none ((of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _
#align generalized_continued_fraction.convergents'_of_int GeneralizedContinuedFraction.convergents'_of_int

variable {K}

/-- The recurrence relation for the `convergents'` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
theorem convergents'_succ :
    (of v).convergents' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convergents' n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convergents'_of_int, fract_intCast, inv_zero, ← cast_zero, convergents'_of_int, cast_zero,
      div_zero, add_zero, floor_intCast]
  · rw [convergents', of_h_eq_floor, add_right_inj, convergents'Aux_succ_some (of_s_head h)]
    exact congr_arg (1 / ·) (by rw [convergents', of_h_eq_floor, add_right_inj, of_s_tail])
#align generalized_continued_fraction.convergents'_succ GeneralizedContinuedFraction.convergents'_succ

end Values

end sequence

end GeneralizedContinuedFraction
