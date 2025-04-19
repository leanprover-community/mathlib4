/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Correctness of Terminating Continued Fraction Computations (`GenContFract.of`)

## Summary

We show the correctness of the algorithm computing continued fractions (`GenContFract.of`)
in case of termination in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(GenContFract.of v).convs' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in `GenContFract.IntFractPair.stream v n`.

For an example, refer to
`GenContFract.compExactValue_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `Algebra.ContinuedFractions.Computation.Basic`.

## Main definitions

- `GenContFract.compExactValue` can be used to compute the exact value approximated by the
  continued fraction `GenContFract.of v` by adding a residual term as described in the summary.

## Main Theorems

- `GenContFract.compExactValue_correctness_of_stream_eq_some` shows that
  `GenContFract.compExactValue` indeed returns the value `v` when given the convergent and
  fractional part as described in the summary.
- `GenContFract.of_correctness_of_terminatedAt` shows the equality
  `v = (GenContFract.of v).convs n` if `GenContFract.of v` terminated at position `n`.
-/

assert_not_exists Finset

namespace GenContFract

open GenContFract (of)

-- `compExactValue_correctness_of_stream_eq_some` does not trivially generalize to `DivisionRing`
variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

/-- Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exactConts.a / exactConts.b` where `exactConts = nextConts 1 fr⁻¹ pconts conts`
  otherwise.

This function can be used to compute the exact value approximated by a continued fraction
`GenContFract.of v` as described in lemma `compExactValue_correctness_of_stream_eq_some`.
-/
protected def compExactValue (pconts conts : Pair K) (fr : K) : K :=
  -- if the fractional part is zero, we exactly approximated the value by the last continuants
  if fr = 0 then
    conts.a / conts.b
  else -- otherwise, we have to include the fractional part in a final continuants step.
    let exactConts := nextConts 1 fr⁻¹ pconts conts
    exactConts.a / exactConts.b

variable [FloorRing K]

/-- Just a computational lemma we need for the next main proof. -/
protected theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp [fract_a_ne_zero]
  rw [Int.fract]
  ring

open GenContFract
  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)

/-- Shows the correctness of `compExactValue` in case the continued fraction
`GenContFract.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `IntFractPair.stream n` to `compExactValue`.

The correctness might be seen more readily if one uses `convs'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `GenContFract.IntFractPair.stream v 0 = some ⟨3, 0.4⟩`, and
- `GenContFract.IntFractPair.stream v 1 = some ⟨2, 0.5⟩`.
Now `(GenContFract.of v).convs' 1 = 3 + 1/2`, and our fractional term at position `2` is `0.5`.
We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`.
This computation corresponds exactly to the one using the recurrence equation in `compExactValue`.
-/
theorem compExactValue_correctness_of_stream_eq_some :
    ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n →
      v = compExactValue ((of v).contsAux n) ((of v).contsAux <| n + 1) ifp_n.fr := by
  let g := of v
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    obtain rfl : IntFractPair.of v = ifp_zero := by
      have : IntFractPair.stream v 0 = some (IntFractPair.of v) := rfl
      simpa only [this, Option.some.injEq] using stream_zero_eq
    cases eq_or_ne (Int.fract v) 0 with
    | inl fract_eq_zero =>
      -- Int.fract v = 0; we must then have `v = ⌊v⌋`
      suffices v = ⌊v⌋ by
        simpa [nextConts, nextNum, nextDen, compExactValue, IntFractPair.of, fract_eq_zero]
      calc
        v = Int.fract v + ⌊v⌋ := by rw [Int.fract_add_floor]
        _ = ⌊v⌋ := by simp [fract_eq_zero]
    | inr fract_ne_zero =>
      -- Int.fract v ≠ 0; the claim then easily follows by unfolding a single computation step
      field_simp [contsAux, nextConts, nextNum, nextDen, of_h_eq_floor, compExactValue,
        IntFractPair.of, fract_ne_zero]
  | succ n IH =>
    intro ifp_succ_n succ_nth_stream_eq
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, -⟩ :
      ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
        ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
      IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
    -- introduce some notation
    let conts := g.contsAux (n + 2)
    set pconts := g.contsAux (n + 1) with pconts_eq
    set ppconts := g.contsAux n with ppconts_eq
    cases eq_or_ne ifp_succ_n.fr 0 with
    | inl ifp_succ_n_fr_eq_zero =>
      -- ifp_succ_n.fr = 0
      suffices v = conts.a / conts.b by simpa [compExactValue, ifp_succ_n_fr_eq_zero]
      -- use the IH and the fact that ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ to prove this case
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
          ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
        IntFractPair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      cases this
      have s_nth_eq : g.s.get? n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero
      rw [← ifp_n_fract_inv_eq_floor] at s_nth_eq
      suffices v = compExactValue ppconts pconts ifp_n.fr by
        simpa [conts, contsAux, s_nth_eq, compExactValue, nth_fract_ne_zero] using this
      exact IH nth_stream_eq
    | inr ifp_succ_n_fr_ne_zero =>
      -- ifp_succ_n.fr ≠ 0
      -- use the IH to show that the following equality suffices
      suffices
        compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts ifp_succ_n.fr by
        have : v = compExactValue ppconts pconts ifp_n.fr := IH nth_stream_eq
        conv_lhs => rw [this]
        assumption
      -- get the correspondence between ifp_n and ifp_succ_n
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨refl⟩⟩ :
        ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
        IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      cases this
      -- get the correspondence between ifp_n and g.s.nth n
      have s_nth_eq : g.s.get? n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero
      -- the claim now follows by unfolding the definitions and tedious calculations
      -- some shorthand notation
      let ppA := ppconts.a
      let ppB := ppconts.b
      let pA := pconts.a
      let pB := pconts.b
      have : compExactValue ppconts pconts ifp_n.fr =
          (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) := by
        -- unfold compExactValue and the convergent computation once
        field_simp [ifp_n_fract_ne_zero, compExactValue, nextConts, nextNum, nextDen, ppA, ppB]
        ac_rfl
      rw [this]
      -- two calculations needed to show the claim
      have tmp_calc :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero
      have tmp_calc' :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero
      let f := Int.fract (1 / ifp_n.fr)
      have f_ne_zero : f ≠ 0 := by simpa [f] using ifp_succ_n_fr_ne_zero
      rw [inv_eq_one_div] at tmp_calc tmp_calc'
      -- because `field_simp` is not as powerful
      have hA : (↑⌊1 / ifp_n.fr⌋ * pA + ppA) + pA * f = pA * (1 / ifp_n.fr) + ppA := by
        have := congrFun (congrArg HMul.hMul tmp_calc) f
        rwa [right_distrib, div_mul_cancel₀ (h := f_ne_zero),
          div_mul_cancel₀ (h := f_ne_zero)] at this
      have hB : (↑⌊1 / ifp_n.fr⌋ * pB + ppB) + pB * f = pB * (1 / ifp_n.fr) + ppB := by
        have := congrFun (congrArg HMul.hMul tmp_calc') f
        rwa [right_distrib, div_mul_cancel₀ (h := f_ne_zero),
          div_mul_cancel₀ (h := f_ne_zero)] at this
      -- now unfold the recurrence one step and simplify both sides to arrive at the conclusion
      dsimp only [conts, pconts, ppconts]
      field_simp [compExactValue, contsAux_recurrence s_nth_eq ppconts_eq pconts_eq,
        nextConts, nextNum, nextDen]
      have hfr : (IntFractPair.of (1 / ifp_n.fr)).fr = f := rfl
      rw [one_div, if_neg _, ← one_div, hfr]
      · field_simp [pA, pB, ppA, ppB, pconts, ppconts, hA, hB]
        ac_rfl
      · rwa [inv_eq_one_div, hfr]

open GenContFract (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)

/-- The convergent of `GenContFract.of v` at step `n - 1` is exactly `v` if the
`IntFractPair.stream` of the corresponding continued fraction terminated at step `n`. -/
theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    v = (of v).convs (n - 1) := by
  induction n with
  | zero => contradiction
  -- IntFractPair.stream v 0 ≠ none
  | succ n IH =>
    let g := of v
    change v = g.convs n
    obtain ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩ :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    · cases n with
      | zero => contradiction
      | succ n' =>
        -- IntFractPair.stream v 0 ≠ none
        have : g.TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
            nth_stream_eq_none
        have : g.convs (n' + 1) = g.convs n' :=
          convs_stable_of_terminated n'.le_succ this
        rw [this]
        exact IH nth_stream_eq_none
    · simpa [nth_stream_fr_eq_zero, compExactValue] using
        compExactValue_correctness_of_stream_eq_some nth_stream_eq

/-- If `GenContFract.of v` terminated at step `n`, then the `n`th convergent is exactly `v`. -/
theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    v = (of v).convs n :=
  have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n
  of_correctness_of_nth_stream_eq_none this

/-- If `GenContFract.of v` terminates, then there is `n : ℕ` such that the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convs n :=
  Exists.elim terminates fun n terminatedAt_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminatedAt_n)

open Filter

/-- If `GenContFract.of v` terminates, then its convergents will eventually always be `v`. -/
theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convs n := by
  rw [eventually_atTop]
  obtain ⟨n, terminatedAt_n⟩ : ∃ n, (of v).TerminatedAt n := terminates
  use n
  intro m m_geq_n
  rw [convs_stable_of_terminated m_geq_n terminatedAt_n]
  exact of_correctness_of_terminatedAt terminatedAt_n

end GenContFract
