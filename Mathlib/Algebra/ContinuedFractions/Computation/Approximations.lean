/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
import Mathlib.Data.Nat.Fib
import Mathlib.Tactic.Monotonicity
import Mathlib.Tactic.SolveByElim

#align_import algebra.continued_fractions.computation.approximations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Approximations for Continued Fraction Computations (`GeneralizedContinuedFraction.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `GeneralizedContinuedFraction.of`. In particular, we derive the so-called
*determinant formula* for `GeneralizedContinuedFraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (GeneralizedContinuedFraction.of v).convergents n|`. The derived bounds will show us that
the error term indeed gets smaller. As a corollary, we will be able to show that
`(GeneralizedContinuedFraction.of v).convergents` converges to `v` in
`Algebra.ContinuedFractions.Computation.ApproximationCorollaries`.

## Main Theorems

- `GeneralizedContinuedFraction.of_part_num_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `GeneralizedContinuedFraction.exists_int_eq_of_part_denom`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `GeneralizedContinuedFraction.of_one_le_get?_part_denom`: shows that `1 ≤ bᵢ`.
- `GeneralizedContinuedFraction.succ_nth_fib_le_of_nth_denom`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `Nat.fib (n + 1)`.
- `GeneralizedContinuedFraction.le_of_succ_get?_denom`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `GeneralizedContinuedFraction.abs_sub_convergents_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the `n`th partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/


namespace GeneralizedContinuedFraction

open GeneralizedContinuedFraction (of)

open Int

variable {K : Type*} {v : K} {n : ℕ} [LinearOrderedField K] [FloorRing K]

namespace IntFractPair

/-!
We begin with some lemmas about the stream of `IntFractPair`s, which presumably are not
of great interest for the end user.
-/


/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
theorem nth_stream_fr_nonneg_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1 := by
  cases n
  -- ⊢ 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1
  case zero =>
    have : IntFractPair.of v = ifp_n := by injection nth_stream_eq
    rw [← this, IntFractPair.of]
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  case succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, ifp_of_eq_ifp_n⟩
    rw [← ifp_of_eq_ifp_n, IntFractPair.of]
    exact ⟨fract_nonneg _, fract_lt_one _⟩
#align generalized_continued_fraction.int_fract_pair.nth_stream_fr_nonneg_lt_one GeneralizedContinuedFraction.IntFractPair.nth_stream_fr_nonneg_lt_one

/-- Shows that the fractional parts of the stream are nonnegative. -/
theorem nth_stream_fr_nonneg {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).left
#align generalized_continued_fraction.int_fract_pair.nth_stream_fr_nonneg GeneralizedContinuedFraction.IntFractPair.nth_stream_fr_nonneg

/-- Shows that the fractional parts of the stream are smaller than one. -/
theorem nth_stream_fr_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).right
#align generalized_continued_fraction.int_fract_pair.nth_stream_fr_lt_one GeneralizedContinuedFraction.IntFractPair.nth_stream_fr_lt_one

/-- Shows that the integer parts of the stream are at least one. -/
theorem one_le_succ_nth_stream_b {ifp_succ_n : IntFractPair K}
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) : 1 ≤ ifp_succ_n.b := by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
    ∃ ifp_n,
      IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n
  exact succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  -- ⊢ 1 ≤ (IntFractPair.of ifp_n.fr⁻¹).b
  suffices 1 ≤ ifp_n.fr⁻¹ by rwa [IntFractPair.of, le_floor, cast_one]
  -- ⊢ 1 ≤ ifp_n.fr⁻¹
  suffices ifp_n.fr ≤ 1 by
    have h : 0 < ifp_n.fr :=
      lt_of_le_of_ne (nth_stream_fr_nonneg nth_stream_eq) stream_nth_fr_ne_zero.symm
    apply one_le_inv h this
  simp only [le_of_lt (nth_stream_fr_lt_one nth_stream_eq)]
  -- 🎉 no goals
#align generalized_continued_fraction.int_fract_pair.one_le_succ_nth_stream_b GeneralizedContinuedFraction.IntFractPair.one_le_succ_nth_stream_b

/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`.
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n)
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ := by
  suffices (⌊ifp_n.fr⁻¹⌋ : K) ≤ ifp_n.fr⁻¹ by
    cases' ifp_n with _ ifp_n_fr
    have : ifp_n_fr ≠ 0 := by
      intro h
      simp [h, IntFractPair.stream, nth_stream_eq] at succ_nth_stream_eq
    have : IntFractPair.of ifp_n_fr⁻¹ = ifp_succ_n := by
      simpa [this, IntFractPair.stream, nth_stream_eq, Option.coe_def] using succ_nth_stream_eq
    rwa [← this]
  exact floor_le ifp_n.fr⁻¹
  -- 🎉 no goals
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_b_le_nth_stream_fr_inv GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv

end IntFractPair

/-!
Next we translate above results about the stream of `IntFractPair`s to the computed continued
fraction `GeneralizedContinuedFraction.of`.
-/


/-- Shows that the integer parts of the continued fraction are at least one. -/
theorem of_one_le_get?_part_denom {b : K}
    (nth_part_denom_eq : (of v).partialDenominators.get? n = some b) : 1 ≤ b := by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b;
  -- ⊢ ∃ gp_n, Stream'.Seq.get? (of v).s n = some gp_n ∧ gp_n.b = b
  exact exists_s_b_of_part_denom nth_part_denom_eq
  -- ⊢ 1 ≤ gp_n.b
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
    ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b
  exact IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  -- ⊢ 1 ≤ gp_n.b
  rw [← ifp_n_b_eq_gp_n_b]
  -- ⊢ 1 ≤ ↑ifp_n.b
  exact_mod_cast IntFractPair.one_le_succ_nth_stream_b succ_nth_stream_eq
  -- 🎉 no goals
#align generalized_continued_fraction.of_one_le_nth_part_denom GeneralizedContinuedFraction.of_one_le_get?_part_denom

/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
theorem of_part_num_eq_one_and_exists_int_part_denom_eq {gp : GeneralizedContinuedFraction.Pair K}
    (nth_s_eq : (of v).s.get? n = some gp) : gp.a = 1 ∧ ∃ z : ℤ, gp.b = (z : K) := by
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ : ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ _
  -- ⊢ ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ ?m.6997 ifp
  exact IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  -- ⊢ gp.a = 1 ∧ ∃ z, gp.b = ↑z
  have : gp = ⟨1, ifp.b⟩ := by
    have : (of v).s.get? n = some ⟨1, ifp.b⟩ :=
      get?_of_eq_some_of_succ_get?_intFractPair_stream stream_succ_nth_eq
    have : some gp = some ⟨1, ifp.b⟩ := by rwa [nth_s_eq] at this
    injection this
  simp [this]
  -- 🎉 no goals
#align generalized_continued_fraction.of_part_num_eq_one_and_exists_int_part_denom_eq GeneralizedContinuedFraction.of_part_num_eq_one_and_exists_int_part_denom_eq

/-- Shows that the partial numerators `aᵢ` are equal to one. -/
theorem of_part_num_eq_one {a : K} (nth_part_num_eq : (of v).partialNumerators.get? n = some a) :
    a = 1 := by
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.a = a;
  -- ⊢ ∃ gp, Stream'.Seq.get? (of v).s n = some gp ∧ gp.a = a
  exact exists_s_a_of_part_num nth_part_num_eq
  -- ⊢ a = 1
  have : gp.a = 1 := (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).left
  -- ⊢ a = 1
  rwa [gp_a_eq_a_n] at this
  -- 🎉 no goals
#align generalized_continued_fraction.of_part_num_eq_one GeneralizedContinuedFraction.of_part_num_eq_one

/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
theorem exists_int_eq_of_part_denom {b : K}
    (nth_part_denom_eq : (of v).partialDenominators.get? n = some b) : ∃ z : ℤ, b = (z : K) := by
  obtain ⟨gp, nth_s_eq, gp_b_eq_b_n⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.b = b;
  -- ⊢ ∃ gp, Stream'.Seq.get? (of v).s n = some gp ∧ gp.b = b
  exact exists_s_b_of_part_denom nth_part_denom_eq
  -- ⊢ ∃ z, b = ↑z
  have : ∃ z : ℤ, gp.b = (z : K) := (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).right
  -- ⊢ ∃ z, b = ↑z
  rwa [gp_b_eq_b_n] at this
  -- 🎉 no goals
#align generalized_continued_fraction.exists_int_eq_of_part_denom GeneralizedContinuedFraction.exists_int_eq_of_part_denom

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `Nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


-- open `Nat` as we will make use of fibonacci numbers.
open Nat

theorem fib_le_of_continuantsAux_b :
    n ≤ 1 ∨ ¬(of v).TerminatedAt (n - 2) → (fib n : K) ≤ ((of v).continuantsAux n).b :=
  Nat.strong_induction_on n
    (by
      intro n IH hyp
      -- ⊢ ↑(fib n) ≤ (continuantsAux (of v) n).b
      rcases n with (_ | _ | n)
      · simp [fib_add_two, continuantsAux] -- case n = 0
        -- 🎉 no goals
      · simp [fib_add_two, continuantsAux] -- case n = 1
        -- 🎉 no goals
      · let g := of v -- case 2 ≤ n
        -- ⊢ ↑(fib (Nat.succ (Nat.succ n))) ≤ (continuantsAux (of v) (Nat.succ (Nat.succ  …
        have : ¬n + 2 ≤ 1 := by linarith
        -- ⊢ ↑(fib (Nat.succ (Nat.succ n))) ≤ (continuantsAux (of v) (Nat.succ (Nat.succ  …
        have not_terminated_at_n : ¬g.TerminatedAt n := Or.resolve_left hyp this
        -- ⊢ ↑(fib (Nat.succ (Nat.succ n))) ≤ (continuantsAux (of v) (Nat.succ (Nat.succ  …
        obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.get? n = some gp
        -- ⊢ ∃ gp, Stream'.Seq.get? g.s n = some gp
        exact Option.ne_none_iff_exists'.mp not_terminated_at_n
        -- ⊢ ↑(fib (Nat.succ (Nat.succ n))) ≤ (continuantsAux (of v) (Nat.succ (Nat.succ  …
        set pconts := g.continuantsAux (n + 1) with pconts_eq
        -- ⊢ ↑(fib (Nat.succ (Nat.succ n))) ≤ (continuantsAux (of v) (Nat.succ (Nat.succ  …
        set ppconts := g.continuantsAux n with ppconts_eq
        -- ⊢ ↑(fib (Nat.succ (Nat.succ n))) ≤ (continuantsAux (of v) (Nat.succ (Nat.succ  …
        -- use the recurrence of `continuantsAux`
        suffices (fib n : K) + fib (n + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b by
          simpa [fib_add_two, add_comm,
            continuantsAux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq]
        -- make use of the fact that `gp.a = 1`
        suffices (fib n : K) + fib (n + 1) ≤ ppconts.b + gp.b * pconts.b by
          simpa [of_part_num_eq_one <| part_num_eq_s_a s_ppred_nth_eq]
        have not_terminated_at_pred_n : ¬g.TerminatedAt (n - 1) :=
          mt (terminated_stable <| Nat.sub_le n 1) not_terminated_at_n
        have not_terminated_at_ppred_n : ¬TerminatedAt g (n - 2) :=
          mt (terminated_stable (n - 1).pred_le) not_terminated_at_pred_n
        -- use the IH to get the inequalities for `pconts` and `ppconts`
        have ppred_nth_fib_le_ppconts_B : (fib n : K) ≤ ppconts.b :=
          IH n (lt_trans (Nat.lt.base n) <| Nat.lt.base <| n + 1) (Or.inr not_terminated_at_ppred_n)
        suffices : (fib (n + 1) : K) ≤ gp.b * pconts.b
        -- ⊢ ↑(fib n) + ↑(fib (n + 1)) ≤ ppconts.b + gp.b * pconts.b
        solve_by_elim [_root_.add_le_add ppred_nth_fib_le_ppconts_B]
        -- ⊢ ↑(fib (n + 1)) ≤ gp.b * pconts.b
        -- finally use the fact that `1 ≤ gp.b` to solve the goal
        suffices 1 * (fib (n + 1) : K) ≤ gp.b * pconts.b by rwa [one_mul] at this
        -- ⊢ 1 * ↑(fib (n + 1)) ≤ gp.b * pconts.b
        have one_le_gp_b : (1 : K) ≤ gp.b :=
          of_one_le_get?_part_denom (part_denom_eq_s_b s_ppred_nth_eq)
        have : (0 : K) ≤ fib (n + 1) := by exact_mod_cast (fib (n + 1)).zero_le
        -- ⊢ 1 * ↑(fib (n + 1)) ≤ gp.b * pconts.b
        have : (0 : K) ≤ gp.b := le_trans zero_le_one one_le_gp_b
        -- ⊢ 1 * ↑(fib (n + 1)) ≤ gp.b * pconts.b
        mono
        -- ⊢ n + 1 < Nat.succ (Nat.succ n)
        · norm_num
          -- 🎉 no goals
        · tauto)
          -- 🎉 no goals
#align generalized_continued_fraction.fib_le_of_continuants_aux_b GeneralizedContinuedFraction.fib_le_of_continuantsAux_b

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `Nat.fib (n + 1) ≤ Bₙ`. -/
theorem succ_nth_fib_le_of_nth_denom (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
    (fib (n + 1) : K) ≤ (of v).denominators n := by
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
  -- ⊢ ↑(fib (n + 1)) ≤ (continuantsAux (of v) (n + 1)).b
  have : n + 1 ≤ 1 ∨ ¬(of v).TerminatedAt (n - 1) := by
    cases' n with n
    case zero => exact Or.inl <| le_refl 1
    case succ => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_of_continuantsAux_b this
  -- 🎉 no goals
#align generalized_continued_fraction.succ_nth_fib_le_of_nth_denom GeneralizedContinuedFraction.succ_nth_fib_le_of_nth_denom

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/


theorem zero_le_of_continuantsAux_b : 0 ≤ ((of v).continuantsAux n).b := by
  let g := of v
  -- ⊢ 0 ≤ (continuantsAux (of v) n).b
  induction' n with n IH
  -- ⊢ 0 ≤ (continuantsAux (of v) zero).b
  case zero => rfl
  -- ⊢ 0 ≤ (continuantsAux (of v) (Nat.succ n)).b
  -- 🎉 no goals
  case succ =>
    cases' Decidable.em <| g.TerminatedAt (n - 1) with terminated not_terminated
    · -- terminating case
      cases' n with n
      · simp [succ_eq_add_one, zero_le_one]
      · have : g.continuantsAux (n + 2) = g.continuantsAux (n + 1) :=
          continuantsAux_stable_step_of_terminated terminated
        simp only [this, IH]
    · -- non-terminating case
      calc
        (0 : K) ≤ fib (n + 1) := by exact_mod_cast (n + 1).fib.zero_le
        _ ≤ ((of v).continuantsAux (n + 1)).b := fib_le_of_continuantsAux_b (Or.inr not_terminated)
#align generalized_continued_fraction.zero_le_of_continuants_aux_b GeneralizedContinuedFraction.zero_le_of_continuantsAux_b

/-- Shows that all denominators are nonnegative. -/
theorem zero_le_of_denom : 0 ≤ (of v).denominators n := by
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]; exact zero_le_of_continuantsAux_b
  -- ⊢ 0 ≤ (continuantsAux (of v) (n + 1)).b
                                                        -- 🎉 no goals
#align generalized_continued_fraction.zero_le_of_denom GeneralizedContinuedFraction.zero_le_of_denom

theorem le_of_succ_succ_get?_continuantsAux_b {b : K}
    (nth_part_denom_eq : (of v).partialDenominators.get? n = some b) :
    b * ((of v).continuantsAux <| n + 1).b ≤ ((of v).continuantsAux <| n + 2).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b
  -- ⊢ ∃ gp_n, Stream'.Seq.get? (of v).s n = some gp_n ∧ gp_n.b = b
  exact exists_s_b_of_part_denom nth_part_denom_eq
  -- ⊢ gp_n.b * (continuantsAux (of v) (n + 1)).b ≤ (continuantsAux (of v) (n + 2)).b
  simp [of_part_num_eq_one (part_num_eq_s_a nth_s_eq), zero_le_of_continuantsAux_b,
    GeneralizedContinuedFraction.continuantsAux_recurrence nth_s_eq rfl rfl]
#align generalized_continued_fraction.le_of_succ_succ_nth_continuants_aux_b GeneralizedContinuedFraction.le_of_succ_succ_get?_continuantsAux_b

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_get?_denom {b : K}
    (nth_part_denom_eq : (of v).partialDenominators.get? n = some b) :
    b * (of v).denominators n ≤ (of v).denominators (n + 1) := by
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
  -- ⊢ b * (continuantsAux (of v) (n + 1)).b ≤ denominators (of v) (n + 1)
  exact le_of_succ_succ_get?_continuantsAux_b nth_part_denom_eq
  -- 🎉 no goals
#align generalized_continued_fraction.le_of_succ_nth_denom GeneralizedContinuedFraction.le_of_succ_get?_denom

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_denom_mono : (of v).denominators n ≤ (of v).denominators (n + 1) := by
  let g := of v
  -- ⊢ denominators (of v) n ≤ denominators (of v) (n + 1)
  cases' Decidable.em <| g.partialDenominators.TerminatedAt n with terminated not_terminated
  -- ⊢ denominators (of v) n ≤ denominators (of v) (n + 1)
  · have : g.partialDenominators.get? n = none := by rwa [Stream'.Seq.TerminatedAt] at terminated
    -- ⊢ denominators (of v) n ≤ denominators (of v) (n + 1)
    have : g.TerminatedAt n :=
      terminatedAt_iff_part_denom_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.denominators (n + 1) = g.denominators n :=
      denominators_stable_of_terminated n.le_succ this
    rw [this]
    -- 🎉 no goals
  · obtain ⟨b, nth_part_denom_eq⟩ : ∃ b, g.partialDenominators.get? n = some b
    -- ⊢ ∃ b, Stream'.Seq.get? (partialDenominators g) n = some b
    exact Option.ne_none_iff_exists'.mp not_terminated
    -- ⊢ denominators (of v) n ≤ denominators (of v) (n + 1)
    have : 1 ≤ b := of_one_le_get?_part_denom nth_part_denom_eq
    -- ⊢ denominators (of v) n ≤ denominators (of v) (n + 1)
    calc
      g.denominators n ≤ b * g.denominators n := by
        simpa using mul_le_mul_of_nonneg_right this zero_le_of_denom
      _ ≤ g.denominators (n + 1) := le_of_succ_get?_denom nth_part_denom_eq
#align generalized_continued_fraction.of_denom_mono GeneralizedContinuedFraction.of_denom_mono

section Determinant

/-!
### Determinant Formula

Next we prove the so-called *determinant formula* for `GeneralizedContinuedFraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.
-/


theorem determinant_aux (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
    ((of v).continuantsAux n).a * ((of v).continuantsAux (n + 1)).b -
      ((of v).continuantsAux n).b * ((of v).continuantsAux (n + 1)).a = (-1) ^ n := by
  induction' n with n IH
  -- ⊢ (continuantsAux (of v) zero).a * (continuantsAux (of v) (zero + 1)).b - (con …
  case zero => simp [continuantsAux]
  -- ⊢ (continuantsAux (of v) (Nat.succ n)).a * (continuantsAux (of v) (Nat.succ n  …
  -- 🎉 no goals
  case succ =>
    -- set up some shorthand notation
    let g := of v
    let conts := continuantsAux g (n + 2)
    set pred_conts := continuantsAux g (n + 1) with pred_conts_eq
    set ppred_conts := continuantsAux g n with ppred_conts_eq
    let pA := pred_conts.a
    let pB := pred_conts.b
    let ppA := ppred_conts.a
    let ppB := ppred_conts.b
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = (-1) ^ (n + 1)
    have not_terminated_at_n : ¬TerminatedAt g n := Or.resolve_left hyp n.succ_ne_zero
    obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp
    exact Option.ne_none_iff_exists'.1 not_terminated_at_n
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices pA * (ppB + gp.b * pB) - pB * (ppA + gp.b * pA) = (-1) ^ (n + 1) by
      simp only [continuantsAux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
      have gp_a_eq_one : gp.a = 1 := of_part_num_eq_one (part_num_eq_s_a s_nth_eq)
      rw [gp_a_eq_one, this.symm]
      ring
    suffices : pA * ppB - pB * ppA = (-1) ^ (n + 1);
    calc
      pA * (ppB + gp.b * pB) - pB * (ppA + gp.b * pA) =
          pA * ppB + pA * gp.b * pB - pB * ppA - pB * gp.b * pA := by ring
      _ = pA * ppB - pB * ppA := by ring
      _ = (-1) ^ (n + 1) := by assumption
    suffices ppA * pB - ppB * pA = (-1) ^ n by
      have pow_succ_n : (-1 : K) ^ (n + 1) = -1 * (-1) ^ n := pow_succ (-1) n
      rw [pow_succ_n, ← this]
      ring
    exact IH <| Or.inr <| mt (terminated_stable <| n.sub_le 1) not_terminated_at_n
#align generalized_continued_fraction.determinant_aux GeneralizedContinuedFraction.determinant_aux

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`. -/
theorem determinant (not_terminated_at_n : ¬(of v).TerminatedAt n) :
    (of v).numerators n * (of v).denominators (n + 1) -
      (of v).denominators n * (of v).numerators (n + 1) = (-1) ^ (n + 1) :=
  determinant_aux <| Or.inr <| not_terminated_at_n
#align generalized_continued_fraction.determinant GeneralizedContinuedFraction.determinant

end Determinant

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (GeneralizedContinuedFraction.of v).convergents n|`.
-/


/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. -/
theorem sub_convergents_eq {ifp : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp) :
    let g := of v
    let B := (g.continuantsAux (n + 1)).b
    let pB := (g.continuantsAux n).b
    v - g.convergents n = if ifp.fr = 0 then 0 else (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) := by
  -- set up some shorthand notation
  let g := of v
  -- ⊢ let g := of v;
  let conts := g.continuantsAux (n + 1)
  -- ⊢ let g := of v;
  let pred_conts := g.continuantsAux n
  -- ⊢ let g := of v;
  have g_finite_correctness :
    v = GeneralizedContinuedFraction.compExactValue pred_conts conts ifp.fr :=
    compExactValue_correctness_of_stream_eq_some stream_nth_eq
  cases' Decidable.em (ifp.fr = 0) with ifp_fr_eq_zero ifp_fr_ne_zero
  · suffices v - g.convergents n = 0 by simpa [ifp_fr_eq_zero]
    -- ⊢ v - convergents g n = 0
    replace g_finite_correctness : v = g.convergents n;
    -- ⊢ v = convergents g n
    · simpa [GeneralizedContinuedFraction.compExactValue, ifp_fr_eq_zero] using g_finite_correctness
      -- 🎉 no goals
    exact sub_eq_zero.2 g_finite_correctness
    -- 🎉 no goals
  · -- more shorthand notation
    let A := conts.a
    -- ⊢ let g := of v;
    let B := conts.b
    -- ⊢ let g := of v;
    let pA := pred_conts.a
    -- ⊢ let g := of v;
    let pB := pred_conts.b
    -- ⊢ let g := of v;
    -- first, let's simplify the goal as `ifp.fr ≠ 0`
    suffices v - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) by simpa [ifp_fr_ne_zero]
    -- ⊢ v - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB))
    -- now we can unfold `g.compExactValue` to derive the following equality for `v`
    replace g_finite_correctness : v = (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B)
    -- ⊢ v = (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B)
    · simpa [GeneralizedContinuedFraction.compExactValue, ifp_fr_ne_zero, nextContinuants,
        nextNumerator, nextDenominator, add_comm] using g_finite_correctness
    -- let's rewrite this equality for `v` in our goal
    suffices
      (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) by
      rwa [g_finite_correctness]
    -- To continue, we need use the determinant equality. So let's derive the needed hypothesis.
    have n_eq_zero_or_not_terminated_at_pred_n : n = 0 ∨ ¬g.TerminatedAt (n - 1) := by
      cases' n with n'
      · simp
      · have : IntFractPair.stream v (n' + 1) ≠ none := by simp [stream_nth_eq]
        have : ¬g.TerminatedAt n' :=
          (not_congr of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 this
        exact Or.inr this
    have determinant_eq : pA * B - pB * A = (-1) ^ n :=
      determinant_aux n_eq_zero_or_not_terminated_at_pred_n
    -- now all we got to do is to rewrite this equality in our goal and re-arrange terms;
    -- however, for this, we first have to derive quite a few tedious inequalities.
    have pB_ineq : (fib n : K) ≤ pB :=
      haveI : n ≤ 1 ∨ ¬g.TerminatedAt (n - 2) := by
        cases' n_eq_zero_or_not_terminated_at_pred_n with n_eq_zero not_terminated_at_pred_n
        · simp [n_eq_zero]
        · exact Or.inr <| mt (terminated_stable (n - 1).pred_le) not_terminated_at_pred_n
      fib_le_of_continuantsAux_b this
    have B_ineq : (fib (n + 1) : K) ≤ B :=
      haveI : n + 1 ≤ 1 ∨ ¬g.TerminatedAt (n + 1 - 2) := by
        cases' n_eq_zero_or_not_terminated_at_pred_n with n_eq_zero not_terminated_at_pred_n
        · simp [n_eq_zero, le_refl]
        · exact Or.inr not_terminated_at_pred_n
      fib_le_of_continuantsAux_b this
    have zero_lt_B : 0 < B :=
      haveI : 1 ≤ B := le_trans
        (by exact_mod_cast fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)) B_ineq
      lt_of_lt_of_le zero_lt_one this
    have zero_ne_B : 0 ≠ B := ne_of_lt zero_lt_B
    -- ⊢ (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B = (-1) ^ n / (B * (ifp.fr⁻ …
    have : 0 ≠ pB + ifp.fr⁻¹ * B := by
      have : (0 : K) ≤ fib n := by exact_mod_cast (fib n).zero_le
      -- 0 ≤ fib n ≤ pB
      have zero_le_pB : 0 ≤ pB := le_trans this pB_ineq
      have : 0 < ifp.fr⁻¹ := by
        suffices 0 < ifp.fr by rwa [inv_pos]
        have : 0 ≤ ifp.fr := IntFractPair.nth_stream_fr_nonneg stream_nth_eq
        change ifp.fr ≠ 0 at ifp_fr_ne_zero
        exact lt_of_le_of_ne this ifp_fr_ne_zero.symm
      have : 0 < ifp.fr⁻¹ * B := mul_pos this zero_lt_B
      have : 0 < pB + ifp.fr⁻¹ * B := add_pos_of_nonneg_of_pos zero_le_pB this
      exact ne_of_lt this
    -- finally, let's do the rewriting
    calc
      (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B =
          ((pA + ifp.fr⁻¹ * A) * B - (pB + ifp.fr⁻¹ * B) * A) / ((pB + ifp.fr⁻¹ * B) * B) := by
        rw [div_sub_div _ _ this.symm zero_ne_B.symm]
      _ = (pA * B + ifp.fr⁻¹ * A * B - (pB * A + ifp.fr⁻¹ * B * A)) / _ := by repeat' rw [add_mul]
      _ = (pA * B - pB * A) / ((pB + ifp.fr⁻¹ * B) * B) := by ring
      _ = (-1) ^ n / ((pB + ifp.fr⁻¹ * B) * B) := by rw [determinant_eq]
      _ = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) := by ac_rfl
#align generalized_continued_fraction.sub_convergents_eq GeneralizedContinuedFraction.sub_convergents_eq

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`. -/
theorem abs_sub_convergents_le (not_terminated_at_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convergents n| ≤ 1 / ((of v).denominators n * ((of v).denominators <| n + 1)) := by
  -- shorthand notation
  let g := of v
  -- ⊢ |v - convergents (of v) n| ≤ 1 / (denominators (of v) n * denominators (of v …
  let nextConts := g.continuantsAux (n + 2)
  -- ⊢ |v - convergents (of v) n| ≤ 1 / (denominators (of v) n * denominators (of v …
  set conts := continuantsAux g (n + 1) with conts_eq
  -- ⊢ |v - convergents (of v) n| ≤ 1 / (denominators (of v) n * denominators (of v …
  set pred_conts := continuantsAux g n with pred_conts_eq
  -- ⊢ |v - convergents (of v) n| ≤ 1 / (denominators (of v) n * denominators (of v …
  -- change the goal to something more readable
  change |v - convergents g n| ≤ 1 / (conts.b * nextConts.b)
  -- ⊢ |v - convergents g n| ≤ 1 / (conts.b * nextConts.b)
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp
  -- ⊢ ∃ gp, Stream'.Seq.get? g.s n = some gp
  exact Option.ne_none_iff_exists'.1 not_terminated_at_n
  -- ⊢ |v - convergents g n| ≤ 1 / (conts.b * nextConts.b)
  have gp_a_eq_one : gp.a = 1 := of_part_num_eq_one (part_num_eq_s_a s_nth_eq)
  -- ⊢ |v - convergents g n| ≤ 1 / (conts.b * nextConts.b)
  -- unfold the recurrence relation for `nextConts.b`
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b := by
    simp [continuantsAux_recurrence s_nth_eq pred_conts_eq conts_eq, gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm]
  let denom := conts.b * (pred_conts.b + gp.b * conts.b)
  -- ⊢ |v - convergents g n| ≤ 1 / (conts.b * nextConts.b)
  suffices |v - g.convergents n| ≤ 1 / denom by rw [nextConts_b_eq]; congr 1
  -- ⊢ |v - convergents g n| ≤ 1 / denom
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
    ∃ ifp_succ_n, IntFractPair.stream v (n + 1) = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b
  exact IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  -- ⊢ |v - convergents g n| ≤ 1 / denom
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
    ∃ ifp_n,
      IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n
  exact IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  -- ⊢ |v - convergents g n| ≤ 1 / denom
  let denom' := conts.b * (pred_conts.b + ifp_n.fr⁻¹ * conts.b)
  -- ⊢ |v - convergents g n| ≤ 1 / denom
  -- now we can use `sub_convergents_eq` to simplify our goal
  suffices |(-1) ^ n / denom'| ≤ 1 / denom by
    have : v - g.convergents n = (-1) ^ n / denom' := by
      -- apply `sub_convergents_eq` and simplify the result
      have tmp := sub_convergents_eq stream_nth_eq
      simp only [stream_nth_fr_ne_zero, conts_eq.symm, pred_conts_eq.symm, if_false] at tmp
      rw [tmp]
      ring
    rwa [this]
  -- derive some tedious inequalities that we need to rewrite our goal
  have nextConts_b_ineq : (fib (n + 2) : K) ≤ pred_conts.b + gp.b * conts.b := by
    have : (fib (n + 2) : K) ≤ nextConts.b :=
      fib_le_of_continuantsAux_b (Or.inr not_terminated_at_n)
    rwa [nextConts_b_eq] at this
  have conts_b_ineq : (fib (n + 1) : K) ≤ conts.b :=
    haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminated_at_n
    fib_le_of_continuantsAux_b <| Or.inr this
  have zero_lt_conts_b : 0 < conts.b :=
    haveI : (0 : K) < fib (n + 1) := by
      exact_mod_cast fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)
    lt_of_lt_of_le this conts_b_ineq
  -- `denom'` is positive, so we can remove `|⬝|` from our goal
  suffices 1 / denom' ≤ 1 / denom by
    have : |(-1) ^ n / denom'| = 1 / denom' := by
      suffices 1 / |denom'| = 1 / denom' by rwa [abs_div, abs_neg_one_pow n]
      have : 0 < denom' := by
        have : 0 ≤ pred_conts.b :=
          haveI : (fib n : K) ≤ pred_conts.b :=
            haveI : ¬g.TerminatedAt (n - 2) :=
              mt (terminated_stable (n.sub_le 2)) not_terminated_at_n
            fib_le_of_continuantsAux_b <| Or.inr this
          le_trans (by exact_mod_cast (fib n).zero_le) this
        have : 0 < ifp_n.fr⁻¹ :=
          haveI zero_le_ifp_n_fract : 0 ≤ ifp_n.fr :=
            IntFractPair.nth_stream_fr_nonneg stream_nth_eq
          inv_pos.2 (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm)
        -- Porting note: replaced complicated positivity proof with tactic.
        positivity
      rw [abs_of_pos this]
    rwa [this]
  suffices 0 < denom ∧ denom ≤ denom' from div_le_div_of_le_left zero_le_one this.left this.right
  -- ⊢ 0 < denom ∧ denom ≤ denom'
  constructor
  -- ⊢ 0 < denom
  · have : 0 < pred_conts.b + gp.b * conts.b :=
      lt_of_lt_of_le
        (by exact_mod_cast fib_pos (lt_of_le_of_ne n.succ.succ.zero_le n.succ.succ_ne_zero.symm))
        nextConts_b_ineq
    solve_by_elim [mul_pos]
    -- 🎉 no goals
  · -- we can cancel multiplication by `conts.b` and addition with `pred_conts.b`
    suffices : gp.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b
    -- ⊢ denom ≤ denom'
    exact (mul_le_mul_left zero_lt_conts_b).2 <| (add_le_add_iff_left pred_conts.b).2 this
    -- ⊢ gp.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b
    suffices (ifp_succ_n.b : K) * conts.b ≤ ifp_n.fr⁻¹ * conts.b by rwa [← ifp_succ_n_b_eq_gp_b]
    -- ⊢ ↑ifp_succ_n.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b
    have : (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ :=
      IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq
    have : 0 ≤ conts.b := le_of_lt zero_lt_conts_b
    -- ⊢ ↑ifp_succ_n.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b
    -- porting note: was `mono`
    refine' mul_le_mul_of_nonneg_right _ _ <;> assumption
    -- ⊢ ↑ifp_succ_n.b ≤ ifp_n.fr⁻¹
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align generalized_continued_fraction.abs_sub_convergents_le GeneralizedContinuedFraction.abs_sub_convergents_le

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`GCF.abs_sub_convergents_le`, but sometimes it is easier to apply and sufficient for one's use case.
 -/
theorem abs_sub_convergents_le' {b : K}
    (nth_part_denom_eq : (of v).partialDenominators.get? n = some b) :
    |v - (of v).convergents n| ≤ 1 / (b * (of v).denominators n * (of v).denominators n) := by
  have not_terminated_at_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_part_denom_none, nth_part_denom_eq]
  refine' (abs_sub_convergents_le not_terminated_at_n).trans _
  -- ⊢ 1 / (denominators (of v) n * denominators (of v) (n + 1)) ≤ 1 / (b * denomin …
  -- One can show that `0 < (GeneralizedContinuedFraction.of v).denominators n` but it's easier
  -- to consider the case `(GeneralizedContinuedFraction.of v).denominators n = 0`.
  rcases (zero_le_of_denom (K := K)).eq_or_gt with
    ((hB : (GeneralizedContinuedFraction.of v).denominators n = 0) | hB)
  · simp only [hB, mul_zero, zero_mul, div_zero, le_refl]
    -- 🎉 no goals
  · apply one_div_le_one_div_of_le
    -- ⊢ 0 < b * denominators (of v) n * denominators (of v) n
    · have : 0 < b := zero_lt_one.trans_le (of_one_le_get?_part_denom nth_part_denom_eq)
      -- ⊢ 0 < b * denominators (of v) n * denominators (of v) n
      apply_rules [mul_pos]
      -- 🎉 no goals
    · conv_rhs => rw [mul_comm]
      -- ⊢ b * denominators (of v) n * denominators (of v) n ≤ denominators (of v) (n + …
      exact mul_le_mul_of_nonneg_right (le_of_succ_get?_denom nth_part_denom_eq) hB.le
      -- 🎉 no goals
#align generalized_continued_fraction.abs_sub_convergents_le' GeneralizedContinuedFraction.abs_sub_convergents_le'

end ErrorTerm

end GeneralizedContinuedFraction
