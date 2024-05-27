/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.ContinuedFractions.ContinuantRecurrence
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

#align_import algebra.continued_fractions.computation.correctness_terminating from "leanprover-community/mathlib"@"d6814c584384ddf2825ff038e868451a7c956f31"

/-!
# Correctness of Terminating Continued Fraction Computations (`CF.of`)

## Summary

We show the correctness of the
algorithm computing continued fractions (`CF.of`) in case of termination
in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(CF.of v).convergents n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in an argument of the corecursor.

For an example, refer to
`CF.compExactValue_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `Algebra.ContinuedFractions.Computation.Basic`.

## Main definitions

- `CF.compExactValue` can be used to compute the exact value
  approximated by the continued fraction `CF.of v` by adding a residual
  term as described in the summary.

## Main Theorems

- `CF.compExactValue_correctness_of_stream_eq_some` shows that
  `CF.compExactValue` indeed returns the value `v` when given the
  convergent and fractional part as described in the summary.
- `CF.of_correctness_of_terminatedAt` shows the equality
  `v = (CF.of v).convergents n` if `CF.of v`
  terminated at position `n`.
-/


namespace CF

open Int Stream' Seq' GCF

open CF (of)

variable {K : Type*} [LinearOrderedField K] [FloorRing K] {v : K} {n : ℕ}

#noalign generalized_continued_fraction.comp_exact_value

#noalign generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some_aux_comp

theorem stream_evalF?_concat_take_fractParts (v : K) :
    Stream'.zipWith
      (fun l w =>
        List.foldrM FGCF.evalF?.next? (some 0)
          (List.map (fun n : ℕ+ => (1, ↑(n : K))) l ++ (w.map ((1, ·⁻¹))).toList))
      (of (fract v)).s.inits (fractParts (fract v)).toStream' =
        const (some (some (fract v))) := by
  refine Stream'.eq_of_bisim
    (fun s₁ s₂ => (∃ (v : K), (0 ≤ v ∧ v < 1) ∧ ∃ (l : List ℕ+),
      s₁ = Stream'.zipWith
        (fun l w =>
          List.foldrM FGCF.evalF?.next? (some 0)
            (List.map (fun n : ℕ+ => (1, ↑(n : K))) l ++ (w.map ((1, ·⁻¹))).toList))
        ↑((of v).s.initsCore l) (fractParts v).toStream' ∧
        s₂ = const (List.foldrM FGCF.evalF?.next? (some 0)
            (List.map (fun n : ℕ+ => (1, ↑(n : K))) l ++
              (if v = 0 then none else some (1, v⁻¹)).toList))) ∨ s₁ = s₂)
    ?_ (Or.inl ⟨fract v, ⟨fract_nonneg v, fract_lt_one v⟩, [], rfl, ?_⟩)
  · rintro _ _ (⟨v, hv, l, rfl, rfl⟩ | rfl)
    case inr => simp
    by_cases hv₂ : v = 0
    case pos =>
      simp [hv₂, Option.bind_eq_bind]
    case neg =>
      simp [fract_eq_self.mpr hv, hv₂, Option.bind_eq_bind, - List.foldrM_append]
      left
      use fract v⁻¹, ⟨fract_nonneg v⁻¹, fract_lt_one v⁻¹⟩, l ++ [⟨⌊v⁻¹⌋₊, of.proof hv hv₂⟩]
      by_cases hv₃ : fract v⁻¹ = 0
      case pos =>
        simp [fract_eq_iff, inv_eq_iff_eq_inv] at hv₃; rcases hv₃ with ⟨n, rfl⟩
        simp [Option.bind_eq_bind]
        lift n to ℕ using by simpa using hv.1
        simp
      case neg =>
        simp [Option.bind_eq_bind, hv₂, hv₃,
          natCast_floor_eq_intCast_floor (inv_nonneg_of_nonneg hv.1)]
  · by_cases hv : fract v = 0 <;> simp [Option.bind_eq_bind, hv, fractParts]

theorem evalF?_concat_take_fractParts
    {w : K} (hw : get? (fractParts v) n = w) :
    (↑((↑((of v).take n) : FSCF K) ++ [w⁻¹]) : FGCF K).evalF? = some v := by
  simp [FGCF.evalF?, - List.foldrM_append]
  use fract v
  simpa [hw, - List.foldrM_append]
    using congr_arg (fun s => get s n) (stream_evalF?_concat_take_fractParts v)

theorem evalF?_eq_of_fractParts_eq_none
    (hv : get? (fractParts v) n = none) : (↑((of v).take n) : FGCF K).evalF? = some v := by
  simp [FGCF.evalF?, - List.foldrM_append]
  use fract v
  simpa [hv, - List.foldrM_append]
    using congr_arg (fun s => get s n) (stream_evalF?_concat_take_fractParts v)

/-- Shows the correctness of `compExactValue` in case the continued fraction
`CF.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `IntFractPair.stream n` to `compExactValue`.

The correctness might be seen more readily if one uses `convergents'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `CF.IntFractPair.stream v 0 = some ⟨3, 0.4⟩`, and
- `CF.IntFractPair.stream v 1 = some ⟨2, 0.5⟩`.
Now `(CF.of v).convergents' 1 = 3 + 1/2`, and our fractional term at
position `2` is `0.5`. We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`. This computation
corresponds exactly to the one using the recurrence equation in `compExactValue`.
-/
theorem fractParts_representation_of_eq_some
    {w : K} (hw : get? (fractParts v) (n + 1) = w) :
    v = (w⁻¹ * ↑(take (n + 1) (of v)).numerator + ↑(take n (of v)).numerator) /
      ↑(w⁻¹ * (take (n + 1) (of v)).denominator + ↑(take n (of v)).denominator) := by
  have hv := evalF?_concat_take_fractParts hw
  obtain ⟨p, hp⟩ : ∃ p, get? (of v).s n = some p
  · suffices hv : ¬(fractParts v).TerminatedAt n by
      simpa [← of_terminatedAt_iff_fractParts_terminatedAt, not_terminatedAt_iff (s := (of v).s),
        Option.isSome_iff_exists] using hv
    apply mt (succ_stable _ (n := _))
    simp [hw]
  simp [← FGCF.eval?_eq_evalF?, CF.take, Seq'.take_succ, hp, FGCF.eval?, ite_eq_iff] at hv
  simp only [← FCF.numerator_toFGCF, ← FCF.denominator_toFGCF]
  simp [CF.take, Seq'.take_succ, hp, hv.2, - FCF.numerator_toFGCF, - FCF.denominator_toFGCF]
#align generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some CF.fractParts_representation_of_eq_some

/-- The convergent of `CF.of v` at step `n - 1` is exactly `v` if the
`IntFractPair.stream` of the corresponding continued fraction terminated at step `n`. -/
theorem fractParts_representation_of_eq_none (hv : get? (fractParts v) n = none) :
    v = (of v).convergents n := by
  replace hv := evalF?_eq_of_fractParts_eq_none hv
  simp [← FGCF.eval?_eq_evalF?, CF.take, FGCF.eval?, ite_eq_iff] at hv
  rw [← Option.some_inj, CF.convergents, ← FCF.eval?_toFGCF, FGCF.eval?]
  simp [CF.take, hv.2, hv.1, - FCF.eval?_toFGCF, - FCF.numerator_toFGCF, - FCF.denominator_toFGCF]
#align generalized_continued_fraction.of_correctness_of_nth_stream_eq_none CF.fractParts_representation_of_eq_none

/-- If `CF.of v` terminated at step `n`, then the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).s.TerminatedAt n) :
    v = (of v).convergents n := by
  rw [of_terminatedAt_iff_fractParts_terminatedAt] at terminatedAt_n
  exact fractParts_representation_of_eq_none terminatedAt_n
#align generalized_continued_fraction.of_correctness_of_terminated_at CF.of_correctness_of_terminatedAt

/-- If `CF.of v` terminates, then there is `n : ℕ` such that the `n`th
convergent is exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).s.Terminates) :
    ∃ n : ℕ, v = (of v).convergents n :=
  Exists.elim terminates fun n terminated_at_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminated_at_n)
#align generalized_continued_fraction.of_correctness_of_terminates CF.of_correctness_of_terminates

open Filter

/-- If `CF.of v` terminates, then its convergents will eventually always
be `v`.
-/
theorem of_correctness_atTop_of_terminates (terminates : (of v).s.Terminates) :
    ∀ᶠ n in atTop, v = (of v).convergents n := by
  rw [eventually_atTop]
  obtain ⟨n, terminated_at_n⟩ : ∃ n, (of v).s.TerminatedAt n
  exact terminates
  use n
  intro m m_geq_n
  rw [convergents_stable m_geq_n terminated_at_n]
  exact of_correctness_of_terminatedAt terminated_at_n
#align generalized_continued_fraction.of_correctness_at_top_of_terminates CF.of_correctness_atTop_of_terminates

end CF
