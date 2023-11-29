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

open Int Seq' GCF

open CF (of)

variable {K : Type*} [LinearOrderedField K] {v : K} {n : ℕ}

/-- Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `(fr⁻¹ * conts.a + pconts.a) / (fr⁻¹ * conts.b + pconts.b)` otherwise.

This function can be used to compute the exact value approximated by a continued fraction
`CF.of v` as described in lemma
`compExactValue_correctness_of_stream_eq_some`.
-/
protected def compExactValue (pconts conts : K × K) (fr : K) : K :=
  -- if the fractional part is zero, we exactly approximated the value by the last continuants
  if fr = 0 then
    conts.1 / conts.2
  else -- otherwise, we have to include the fractional part in a final continuants step.
    (fr⁻¹ * conts.1 + pconts.1) / (fr⁻¹ * conts.2 + pconts.2)
#align generalized_continued_fraction.comp_exact_value CF.compExactValue

variable [FloorRing K]

/-- Just a computational lemma we need for the next main proof. -/
protected theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp [fract_a_ne_zero]
  rw [Int.fract]
  ring
#align generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some_aux_comp CF.compExactValue_correctness_of_stream_eq_some_aux_comp

open CF
  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)

theorem seq_evalF?_concat_take_fractParts (v : K) :
    zipWith
      (fun l w =>
        List.foldrM FGCF.evalF?.next? (some 0)
          (List.map (fun n : ℕ+ => (1, ↑(n : K))) l ++ [(1, w⁻¹)]))
      ↑(of v).s.inits (fractParts v) =
        (fractParts v).map
          (fun _ => some (some (fract v))) := by
  refine eq_of_bisim
    (fun s₁ s₂ => ∃ (v : K) (hv : 0 ≤ v ∧ v < 1) (l : List ℕ+),
      s₁ = zipWith
        (fun l w =>
          List.foldrM FGCF.evalF?.next? (some 0)
            (List.map (fun n : ℕ+ => (1, ↑(n : K))) l ++ [(1, w⁻¹)]))
        ↑((corec of.next? ⟨v, hv⟩).initsCore l) (corec fractParts.next? v) ∧
        s₂ = (corec fractParts.next? v).map
          (fun _ => List.foldrM FGCF.evalF?.next? (some 0)
            (List.map (fun n : ℕ+ => (1, ↑(n : K))) l ++ [(1, v⁻¹)])))
    ?_ ⟨fract v, ⟨fract_nonneg v, fract_lt_one v⟩, [], rfl, ?_⟩
  · rintro _ _ ⟨v, hv, l, rfl, rfl⟩
    by_cases hv₂ : v = 0
    case pos => simp [hv₂]
    case neg =>
      simp [fract_eq_self.mpr hv, hv₂, Option.bind_eq_bind, - List.foldrM_append]
      have hvo : 0 < ⌊v⁻¹⌋₊ := by
        rcases hv with ⟨hvge, hvlt⟩
        rw [Nat.floor_pos, one_le_inv_iff, lt_iff_le_and_ne, ne_comm]
        exact ⟨⟨hvge, hv₂⟩, le_of_lt hvlt⟩
      use fract v⁻¹, ⟨fract_nonneg v⁻¹, fract_lt_one v⁻¹⟩, l ++ [⟨⌊v⁻¹⌋₊, hvo⟩]
      by_cases hv₃ : fract v⁻¹ = 0
      case pos =>
        simp [Option.bind_eq_bind, hv₂, hv₃]
        apply dest_injective
        simp
      case neg =>
        simp [Option.bind_eq_bind, hv₂, hv₃,
          Nat.cast_floor_eq_cast_int_floor (inv_nonneg_of_nonneg hv.1)]
  · by_cases hv : fract v = 0 <;> simp [Option.bind_eq_bind, hv, fractParts]
    apply dest_injective
    simp

theorem evalF?_concat_take_fractParts
    {w : K} (hw : get? (fractParts v) n = w) :
    (⟨↑⌊v⌋, (take n (↑(of v) : GCF K)).l ++ [(1, w⁻¹)]⟩ : FGCF K).evalF? = some v := by
  simp [FGCF.evalF?, - List.foldrM_append]
  use fract v
  simpa [hw, - List.foldrM_append]
    using congr_arg (fun s => get? s n) (seq_evalF?_concat_take_fractParts v)

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
theorem fractParts_representation
    {w : K} (hw : get? (fractParts v) (n + 1) = w) :
    v = (w⁻¹ * (take (n + 1) ↑(of v)).numerator + (take n ↑(of v)).numerator) /
      (w⁻¹ * (take (n + 1) ↑(of v)).denominator + (take n ↑(of v)).denominator) := by
  have hv := evalF?_concat_take_fractParts hw
  obtain ⟨p, hp⟩ : ∃ p, get? (of v).s n = some p
  · suffices hv : ¬(fractParts v).TerminatedAt n
    · simpa [← of_terminatedAt_iff_fractParts_terminatedAt,
        terminatedAt_iff_s_terminatedAt, not_terminatedAt_iff (s := (of v).s),
        Option.isSome_iff_exists] using hv
    apply mt (succ_stable _ (n := _))
    simp [hw]
  simp [← FGCF.eval?_eq_evalF?, take_succ, hp, FGCF.eval?, ite_eq_iff] at hv
  simp [GCF.take, take_succ, hp, hv.2]
#align generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some CF.fractParts_representation

open CF (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)

/-- The convergent of `CF.of v` at step `n - 1` is exactly `v` if the
`IntFractPair.stream` of the corresponding continued fraction terminated at step `n`. -/
theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    v = (of v).convergents (n - 1) := by
  induction n with
  | zero => contradiction
  -- IntFractPair.stream v 0 ≠ none
  | succ n IH =>
    let g := of v
    change v = g.convergents n
    have :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    rcases this with (⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩)
    · cases' n with n'
      · contradiction
      -- IntFractPair.stream v 0 ≠ none
      · have : g.TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
            nth_stream_eq_none
        have : g.convergents (n' + 1) = g.convergents n' :=
          convergents_stable_of_terminated n'.le_succ this
        rw [this]
        exact IH nth_stream_eq_none
    · simpa [nth_stream_fr_eq_zero, compExactValue] using
        compExactValue_correctness_of_stream_eq_some nth_stream_eq
#align generalized_continued_fraction.of_correctness_of_nth_stream_eq_none CF.of_correctness_of_nth_stream_eq_none

/-- If `CF.of v` terminated at step `n`, then the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminatedAt (terminated_at_n : (of v).TerminatedAt n) :
    v = (of v).convergents n :=
  have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminated_at_n
  of_correctness_of_nth_stream_eq_none this
#align generalized_continued_fraction.of_correctness_of_terminated_at CF.of_correctness_of_terminatedAt

/-- If `CF.of v` terminates, then there is `n : ℕ` such that the `n`th
convergent is exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convergents n :=
  Exists.elim terminates fun n terminated_at_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminated_at_n)
#align generalized_continued_fraction.of_correctness_of_terminates CF.of_correctness_of_terminates

open Filter

/-- If `CF.of v` terminates, then its convergents will eventually always
be `v`.
-/
theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convergents n := by
  rw [eventually_atTop]
  obtain ⟨n, terminated_at_n⟩ : ∃ n, (of v).TerminatedAt n
  exact terminates
  use n
  intro m m_geq_n
  rw [convergents_stable_of_terminated m_geq_n terminated_at_n]
  exact of_correctness_of_terminatedAt terminated_at_n
#align generalized_continued_fraction.of_correctness_at_top_of_terminates CF.of_correctness_atTop_of_terminates

end CF
