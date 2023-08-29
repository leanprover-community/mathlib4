/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic.FieldSimp

#align_import algebra.continued_fractions.computation.correctness_terminating from "leanprover-community/mathlib"@"d6814c584384ddf2825ff038e868451a7c956f31"

/-!
# Correctness of Terminating Continued Fraction Computations (`GeneralizedContinuedFraction.of`)

## Summary

We show the correctness of the
algorithm computing continued fractions (`GeneralizedContinuedFraction.of`) in case of termination
in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(GeneralizedContinuedFraction.of v).convergents' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in
`GeneralizedContinuedFraction.IntFractPair.stream v n`.

For an example, refer to
`GeneralizedContinuedFraction.compExactValue_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `Algebra.ContinuedFractions.Computation.Basic`.

## Main definitions

- `GeneralizedContinuedFraction.compExactValue` can be used to compute the exact value
  approximated by the continued fraction `GeneralizedContinuedFraction.of v` by adding a residual
  term as described in the summary.

## Main Theorems

- `GeneralizedContinuedFraction.compExactValue_correctness_of_stream_eq_some` shows that
  `GeneralizedContinuedFraction.compExactValue` indeed returns the value `v` when given the
  convergent and fractional part as described in the summary.
- `GeneralizedContinuedFraction.of_correctness_of_terminatedAt` shows the equality
  `v = (GeneralizedContinuedFraction.of v).convergents n` if `GeneralizedContinuedFraction.of v`
  terminated at position `n`.
-/


namespace GeneralizedContinuedFraction

open GeneralizedContinuedFraction (of)

variable {K : Type*} [LinearOrderedField K] {v : K} {n : ℕ}

/-- Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exact_conts.a / exact_conts.b` where `exact_conts = nextContinuants 1 fr⁻¹ pconts conts`
  otherwise.

This function can be used to compute the exact value approximated by a continued fraction
`GeneralizedContinuedFraction.of v` as described in lemma
`compExactValue_correctness_of_stream_eq_some`.
-/
protected def compExactValue (pconts conts : Pair K) (fr : K) : K :=
  -- if the fractional part is zero, we exactly approximated the value by the last continuants
  if fr = 0 then
    conts.a / conts.b
  else -- otherwise, we have to include the fractional part in a final continuants step.
    let exact_conts := nextContinuants 1 fr⁻¹ pconts conts
    exact_conts.a / exact_conts.b
#align generalized_continued_fraction.comp_exact_value GeneralizedContinuedFraction.compExactValue

variable [FloorRing K]

/-- Just a computational lemma we need for the next main proof. -/
protected theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp [fract_a_ne_zero]
  -- ⊢ ↑⌊a⌋ * b + c + b * Int.fract a = b * a + c
  rw [Int.fract]
  -- ⊢ ↑⌊a⌋ * b + c + b * (a - ↑⌊a⌋) = b * a + c
  ring
  -- 🎉 no goals
#align generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some_aux_comp GeneralizedContinuedFraction.compExactValue_correctness_of_stream_eq_some_aux_comp

open GeneralizedContinuedFraction
  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)

/-- Shows the correctness of `compExactValue` in case the continued fraction
`GeneralizedContinuedFraction.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `IntFractPair.stream n` to `compExactValue`.

The correctness might be seen more readily if one uses `convergents'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `GeneralizedContinuedFraction.IntFractPair.stream v 0 = some ⟨3, 0.4⟩`, and
- `GeneralizedContinuedFraction.IntFractPair.stream v 1 = some ⟨2, 0.5⟩`.
Now `(GeneralizedContinuedFraction.of v).convergents' 1 = 3 + 1/2`, and our fractional term at
position `2` is `0.5`. We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`. This computation
corresponds exactly to the one using the recurrence equation in `compExactValue`.
-/
theorem compExactValue_correctness_of_stream_eq_some :
    ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n →
      v = compExactValue ((of v).continuantsAux n) ((of v).continuantsAux <| n + 1) ifp_n.fr := by
  let g := of v
  -- ⊢ ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n → v = compE …
  induction' n with n IH
  -- ⊢ ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v Nat.zero = some ifp_n → v  …
  · intro ifp_zero stream_zero_eq
    -- ⊢ v = compExactValue (continuantsAux (of v) Nat.zero) (continuantsAux (of v) ( …
    -- Nat.zero
    have : IntFractPair.of v = ifp_zero := by
      have : IntFractPair.stream v 0 = some (IntFractPair.of v) := rfl
      simpa only [Nat.zero_eq, this, Option.some.injEq] using stream_zero_eq
    cases this
    -- ⊢ v = compExactValue (continuantsAux (of v) Nat.zero) (continuantsAux (of v) ( …
    cases' Decidable.em (Int.fract v = 0) with fract_eq_zero fract_ne_zero
    -- ⊢ v = compExactValue (continuantsAux (of v) Nat.zero) (continuantsAux (of v) ( …
    -- Int.fract v = 0; we must then have `v = ⌊v⌋`
    · suffices v = ⌊v⌋ by
        -- Porting note: was `simpa [continuantsAux, fract_eq_zero, compExactValue]`
        field_simp [nextContinuants, nextNumerator, nextDenominator, compExactValue]
        have : (IntFractPair.of v).fr = Int.fract v := rfl
        rwa [this, if_pos fract_eq_zero]
      calc
        v = Int.fract v + ⌊v⌋ := by rw [Int.fract_add_floor]
        _ = ⌊v⌋ := by simp [fract_eq_zero]
    -- Int.fract v ≠ 0; the claim then easily follows by unfolding a single computation step
    · field_simp [continuantsAux, nextContinuants, nextNumerator, nextDenominator,
        of_h_eq_floor, compExactValue]
      -- Porting note: this and the if_neg rewrite are needed
      have : (IntFractPair.of v).fr = Int.fract v := rfl
      -- ⊢ v = if (IntFractPair.of v).fr = 0 then ↑⌊v⌋ else ↑⌊v⌋ + (IntFractPair.of v).fr
      rw [this, if_neg fract_ne_zero, Int.floor_add_fract]
      -- 🎉 no goals
  · intro ifp_succ_n succ_nth_stream_eq
    -- ⊢ v = compExactValue (continuantsAux (of v) (Nat.succ n)) (continuantsAux (of  …
    -- Nat.succ
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, -⟩ :
      ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
        ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n
    exact IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
    -- ⊢ v = compExactValue (continuantsAux (of v) (Nat.succ n)) (continuantsAux (of  …
    -- introduce some notation
    let conts := g.continuantsAux (n + 2)
    -- ⊢ v = compExactValue (continuantsAux (of v) (Nat.succ n)) (continuantsAux (of  …
    set pconts := g.continuantsAux (n + 1) with pconts_eq
    -- ⊢ v = compExactValue pconts (continuantsAux (of v) (Nat.succ n + 1)) ifp_succ_ …
    set ppconts := g.continuantsAux n with ppconts_eq
    -- ⊢ v = compExactValue pconts (continuantsAux (of v) (Nat.succ n + 1)) ifp_succ_ …
    cases' Decidable.em (ifp_succ_n.fr = 0) with ifp_succ_n_fr_eq_zero ifp_succ_n_fr_ne_zero
    -- ⊢ v = compExactValue pconts (continuantsAux (of v) (Nat.succ n + 1)) ifp_succ_ …
    -- ifp_succ_n.fr = 0
    · suffices v = conts.a / conts.b by simpa [compExactValue, ifp_succ_n_fr_eq_zero]
      -- ⊢ v = conts.a / conts.b
      -- use the IH and the fact that ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ to prove this case
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
        ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋
      exact IntFractPair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero
      -- ⊢ v = conts.a / conts.b
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      -- ⊢ v = conts.a / conts.b
      cases this
      -- ⊢ v = conts.a / conts.b
      have s_nth_eq : g.s.get? n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero
      rw [← ifp_n_fract_inv_eq_floor] at s_nth_eq
      -- ⊢ v = conts.a / conts.b
      suffices v = compExactValue ppconts pconts ifp_n.fr by
        simpa [continuantsAux, s_nth_eq, compExactValue, nth_fract_ne_zero] using this
      exact IH nth_stream_eq
      -- 🎉 no goals
    -- ifp_succ_n.fr ≠ 0
    · -- use the IH to show that the following equality suffices
      suffices
        compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts ifp_succ_n.fr by
        have : v = compExactValue ppconts pconts ifp_n.fr := IH nth_stream_eq
        conv_lhs => rw [this]
        assumption
      -- get the correspondence between ifp_n and ifp_succ_n
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨refl⟩⟩ :
        ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n
      exact IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      cases this
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      -- get the correspondence between ifp_n and g.s.nth n
      have s_nth_eq : g.s.get? n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero
      -- the claim now follows by unfolding the definitions and tedious calculations
      -- some shorthand notation
      let ppA := ppconts.a
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      let ppB := ppconts.b
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      let pA := pconts.a
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      let pB := pconts.b
      -- ⊢ compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts (IntFra …
      have : compExactValue ppconts pconts ifp_n.fr =
          (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) := by
        -- unfold compExactValue and the convergent computation once
        field_simp [ifp_n_fract_ne_zero, compExactValue, nextContinuants, nextNumerator,
          nextDenominator]
        ac_rfl
      rw [this]
      -- ⊢ (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) = compExactValue pconts co …
      -- two calculations needed to show the claim
      have tmp_calc :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero
      have tmp_calc' :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero
      let f := Int.fract (1 / ifp_n.fr)
      -- ⊢ (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) = compExactValue pconts co …
      have f_ne_zero : f ≠ 0 := by simpa using ifp_succ_n_fr_ne_zero
      -- ⊢ (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) = compExactValue pconts co …
      rw [inv_eq_one_div] at tmp_calc tmp_calc'
      -- ⊢ (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) = compExactValue pconts co …
      -- Porting note: the `tmp_calc`s need to be massaged, and some processing after `ac_rfl` done,
      -- because `field_simp` is not as powerful
      have hA : (↑⌊1 / ifp_n.fr⌋ * pA + ppA) + pA * f = pA * (1 / ifp_n.fr) + ppA := by
        have := congrFun (congrArg HMul.hMul tmp_calc) f
        rwa [right_distrib, div_mul_cancel (h := f_ne_zero),
          div_mul_cancel (h := f_ne_zero)] at this
      have hB : (↑⌊1 / ifp_n.fr⌋ * pB + ppB) + pB * f = pB * (1 / ifp_n.fr) + ppB := by
        have := congrFun (congrArg HMul.hMul tmp_calc') f
        rwa [right_distrib, div_mul_cancel (h := f_ne_zero),
          div_mul_cancel (h := f_ne_zero)] at this
      -- now unfold the recurrence one step and simplify both sides to arrive at the conclusion
      field_simp [compExactValue, continuantsAux_recurrence s_nth_eq ppconts_eq pconts_eq,
        nextContinuants, nextNumerator, nextDenominator]
      have hfr : (IntFractPair.of (1 / ifp_n.fr)).fr = f := rfl
      -- ⊢ ((continuantsAux (of v) n).a * ifp_n.fr + (continuantsAux (of v) (n + 1)).a) …
      rw [one_div, if_neg _, ← one_div, hfr]
      -- ⊢ ((continuantsAux (of v) n).a * ifp_n.fr + (continuantsAux (of v) (n + 1)).a) …
      field_simp [hA, hB]
      -- ⊢ ((continuantsAux (of v) n).a * ifp_n.fr + (continuantsAux (of v) (n + 1)).a) …
      ac_rfl
      -- ⊢ ¬(IntFractPair.of ifp_n.fr⁻¹).fr = 0
      rwa [inv_eq_one_div, hfr]
      -- 🎉 no goals
#align generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some GeneralizedContinuedFraction.compExactValue_correctness_of_stream_eq_some

open GeneralizedContinuedFraction (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)

/-- The convergent of `GeneralizedContinuedFraction.of v` at step `n - 1` is exactly `v` if the
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
#align generalized_continued_fraction.of_correctness_of_nth_stream_eq_none GeneralizedContinuedFraction.of_correctness_of_nth_stream_eq_none

/-- If `GeneralizedContinuedFraction.of v` terminated at step `n`, then the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminatedAt (terminated_at_n : (of v).TerminatedAt n) :
    v = (of v).convergents n :=
  have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminated_at_n
  of_correctness_of_nth_stream_eq_none this
#align generalized_continued_fraction.of_correctness_of_terminated_at GeneralizedContinuedFraction.of_correctness_of_terminatedAt

/-- If `GeneralizedContinuedFraction.of v` terminates, then there is `n : ℕ` such that the `n`th
convergent is exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convergents n :=
  Exists.elim terminates fun n terminated_at_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminated_at_n)
#align generalized_continued_fraction.of_correctness_of_terminates GeneralizedContinuedFraction.of_correctness_of_terminates

open Filter

/-- If `GeneralizedContinuedFraction.of v` terminates, then its convergents will eventually always
be `v`.
-/
theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convergents n := by
  rw [eventually_atTop]
  -- ⊢ ∃ a, ∀ (b : ℕ), b ≥ a → v = convergents (of v) b
  obtain ⟨n, terminated_at_n⟩ : ∃ n, (of v).TerminatedAt n
  -- ⊢ ∃ n, TerminatedAt (of v) n
  exact terminates
  -- ⊢ ∃ a, ∀ (b : ℕ), b ≥ a → v = convergents (of v) b
  use n
  -- ⊢ ∀ (b : ℕ), b ≥ n → v = convergents (of v) b
  intro m m_geq_n
  -- ⊢ v = convergents (of v) m
  rw [convergents_stable_of_terminated m_geq_n terminated_at_n]
  -- ⊢ v = convergents (of v) n
  exact of_correctness_of_terminatedAt terminated_at_n
  -- 🎉 no goals
#align generalized_continued_fraction.of_correctness_at_top_of_terminates GeneralizedContinuedFraction.of_correctness_atTop_of_terminates

end GeneralizedContinuedFraction
