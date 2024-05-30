/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Monotonicity
import Mathlib.Algebra.GroupPower.Order

#align_import algebra.continued_fractions.computation.approximations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Approximations for Continued Fraction Computations (`GeneralizedContinuedFraction.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `GeneralizedContinuedFraction.of`. In particular, we derive the so-called
*determinant formula* for simple continued fractions:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (GeneralizedContinuedFraction.of v).convergents n|`. The derived bounds will show us that
the error term indeed gets smaller. As a corollary, we will be able to show that
`(GeneralizedContinuedFraction.of v).convergents` converges to `v` in
`Algebra.ContinuedFractions.Computation.ApproximationCorollaries`.

## Main Theorems

- `GeneralizedContinuedFraction.of_partNum_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `GeneralizedContinuedFraction.exists_int_eq_of_partDenom`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `GeneralizedContinuedFraction.of_one_le_get?_partDenom`: shows that `1 ≤ bᵢ`.
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


open Int List Seq'

variable {K : Type*}

namespace CF

open CF (of)

variable [LinearOrderedField K] [FloorRing K] {v : K} {n : ℕ}

/-!
We begin with some lemmas about the stream of `IntFractPair`s, which presumably are not
of great interest for the end user.
-/


/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
theorem fractParts_pos_lt_one {w : K}
    (hw : get? (fractParts v) n = some w) : 0 < w ∧ w < 1 := by
  suffices hv : All (fun w => 0 < w ∧ w < 1) (fractParts v) by
    rw [all_iff] at hv
    exact hv _ ⟨n, hw⟩
  refine ⟨fun s => ∃ v, s = fractParts v, ⟨v, rfl⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  by_cases hv : fract v = 0 <;> simp [hv, fract_lt_one]
  exact lt_of_le_of_ne (fract_nonneg v) (Ne.symm hv)
#align generalized_continued_fraction.int_fract_pair.nth_stream_fr_nonneg_lt_one CF.fractParts_pos_lt_one

/-- Shows that the fractional parts of the stream are nonnegative. -/
theorem fractParts_pos {w : K}
    (hw : get? (fractParts v) n = some w) : 0 < w :=
  (fractParts_pos_lt_one hw).left
#align generalized_continued_fraction.int_fract_pair.nth_stream_fr_nonneg CF.fractParts_pos

/-- Shows that the fractional parts of the stream are smaller than one. -/
theorem fractParts_lt_one {w : K}
    (hw : get? (fractParts v) n = some w) : w < 1 :=
  (fractParts_pos_lt_one hw).right
#align generalized_continued_fraction.int_fract_pair.nth_stream_fr_lt_one CF.fractParts_lt_one

#noalign generalized_continued_fraction.int_fract_pair.one_le_succ_nth_stream_b

/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`.
-/
theorem of_s_le_inv_fractParts {m : ℕ+} {w : K}
    (hm : get? (of v).s n = m) (hw : get? (fractParts v) n = w) : (↑m : K) ≤ w⁻¹ := by
  have hv :=
    congr_arg (fun s => Seq'.get? s n) (map_coe_of_s_eq_map_nat_floor_comp_inv_fractParts v)
  simp [hm, hw] at hv
  simp [hv]
  exact Nat.floor_le (inv_nonneg_of_nonneg (le_of_lt (fractParts_pos hw)))
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_b_le_nth_stream_fr_inv CF.of_s_le_inv_fractParts

/-!
Next we translate above results about the stream of `IntFractPair`s to the computed continued
fraction `GeneralizedContinuedFraction.of`.
-/


#noalign generalized_continued_fraction.of_one_le_nth_part_denom

#noalign generalized_continued_fraction.of_part_num_eq_one_and_exists_int_part_denom_eq

#noalign generalized_continued_fraction.of_part_num_eq_one

#noalign generalized_continued_fraction.of_is_simple_continued_fraction

#noalign simple_continued_fraction.of

#noalign simple_continued_fraction.of_is_continued_fraction

#noalign continued_fraction.of

#noalign generalized_continued_fraction.exists_int_eq_of_part_denom

end CF

namespace FCF

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `Nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


-- open `Nat` as we will make use of fibonacci numbers.
open Nat

#noalign generalized_continued_fraction.fib_le_of_continuants_aux_b

theorem succ_length_fib_le_denom (f : FCF K) : fib (f.l.length + 1) ≤ ↑f.denominator := by
  rcases f with ⟨h, l⟩
  rcases eq_nil_or_concat l with rfl | ⟨l, n₂, rfl⟩
  · simp
  · rcases eq_nil_or_concat l with rfl | ⟨l, n₁, rfl⟩
    · simp [show 1 + 1 = 2 from rfl]
      norm_cast; apply PNat.one_le
    · rw [show (l ++ [n₁] ++ [n₂]).length + 1 = l.length + 1 + 2 by simp, fib_add_two]
      simp
      conv_rhs => rw [add_comm]
      apply Nat.add_le_add
      · simpa using succ_length_fib_le_denom (⟨h, l⟩ : FCF K)
      · trans
        · simpa using succ_length_fib_le_denom (⟨h, l ++ [n₁]⟩ : FCF K)
        · norm_cast
          simp
termination_by f.l.length
#align generalized_continued_fraction.succ_nth_fib_le_of_nth_denom FCF.succ_length_fib_le_denom

#noalign generalized_continued_fraction.zero_le_of_continuants_aux_b

#noalign generalized_continued_fraction.zero_le_of_denom

#noalign generalized_continued_fraction.le_of_succ_succ_nth_continuants_aux_b

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem mul_denom_le_concat_denom (f : FCF K) (n : ℕ+) :
    n * f.denominator ≤ (f ++ [n]).denominator := by
  rcases f with ⟨h, l⟩
  rcases eq_nil_or_concat l with rfl | ⟨l, n₁, rfl⟩
  · simp
  · simp
    apply le_of_lt; apply PNat.lt_add_right
#align generalized_continued_fraction.le_of_succ_nth_denom FCF.mul_denom_le_concat_denom

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem denom_mono (f : FCF K) (n : ℕ+) : f.denominator ≤ (f ++ [n]).denominator := by
  trans n * f.denominator
  · simp only [le_mul_iff_one_le_left', PNat.one_le]
  · apply mul_denom_le_concat_denom
#align generalized_continued_fraction.of_denom_mono FCF.denom_mono

end FCF

section Determinant

/-!
### Determinant Formula

Next we prove the so-called *determinant formula* for simple continued fractions:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.
-/

namespace FGCF

variable [Field K]

#noalign generalized_continued_fraction.determinant_aux

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`. -/
theorem determinant (f : FGCF K) (p : K × K) :
    f.numerator * (f ++ [p]).denominator -
      f.denominator * (f ++ [p]).numerator = (f.l.map (fun p => - p.1)).prod * - p.1 := by
  rcases f with ⟨h, l⟩
  rcases eq_nil_or_concat l with rfl | ⟨l, p₁, rfl⟩
  · simp
    ring
  · have hf := determinant ⟨h, l⟩ p₁; simp at hf
    simp [← hf]
    ring
termination_by f.l.length
#align generalized_continued_fraction.determinant FGCF.determinant

end FGCF

namespace FSCF

variable [Field K]

theorem determinant (f : FSCF K) (v : K) :
    (↑f : FGCF K).numerator * (↑(f ++ [v]) : FGCF K).denominator -
      (↑f : FGCF K).denominator * (↑(f ++ [v]) : FGCF K).numerator =
        (-1) ^ (f.l.length + 1) := by
  simpa [Function.comp, pow_succ] using FGCF.determinant (↑f : FGCF K) (1, v)

end FSCF

namespace FCF

theorem determinant (f : FCF K) (n : ℕ+) :
    f.numerator * ↑(f ++ [n]).denominator -
      ↑f.denominator * (f ++ [n]).numerator = (-1) ^ (f.l.length + 1) := by
  rcases f with ⟨h, l⟩
  rcases eq_nil_or_concat l with rfl | ⟨l, p₁, rfl⟩
  · simp
    ring
  · have hf := determinant ⟨h, l⟩ p₁; simp [pow_succ] at hf
    simp [← hf, pow_succ]
    ring
termination_by f.l.length

end FCF

end Determinant

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (GeneralizedContinuedFraction.of v).convergents n|`.
-/

namespace CF

open CF (of)

variable [LinearOrderedField K] [FloorRing K] {v : K} {n : ℕ}


/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. -/
theorem sub_convergents_eq {w : K} (hw : get? (fractParts v) (n + 1) = some w) :
    v - (of v).convergents (n + 1) =
      (-1) ^ (n + 1) / (↑(take (n + 1) (of v)).denominator *
        (w⁻¹ * ↑(take (n + 1) (of v)).denominator + ↑(take n (of v)).denominator)) := by
  have hnz₁ := ne_of_gt (fractParts_pos hw)
  have hnz₂ : (↑(take (n + 1) (of v)).denominator : K) ≠ 0 :=
    mod_cast ne_of_gt (take (n + 1) (of v)).denominator.pos
  have hnz₃ : ↑(take (n + 1) (of v)).denominator + ↑(take n (of v)).denominator * w ≠ 0 := by
    apply ne_of_gt
    apply add_pos
    · exact mod_cast (take (n + 1) (of v)).denominator.pos
    · apply mul_pos
      · exact mod_cast (take n (of v)).denominator.pos
      · exact fractParts_pos hw
  obtain ⟨p, hp⟩ : ∃ p, get? (of v).s n = some p
  · suffices hv : ¬(fractParts v).TerminatedAt n by
      simpa [← of_terminatedAt_iff_fractParts_terminatedAt, not_terminatedAt_iff (s := (of v).s),
        Option.isSome_iff_exists] using hv
    apply mt (succ_stable _ (n := _))
    simp [hw]
  have hp₂ : take n (of v) ++ [p] = take (n + 1) (of v) := by
    simp [CF.take, Seq'.take_succ, hp]
  conv_lhs =>
    arg 1
    rw [fractParts_representation_of_eq_some hw]
  have hv₁ : ((of v).s.take n).length = n := by
    suffices hv : ∀ m, ((of v).s.take n).get? m = none ↔ n ≤ m by
      simp [- Seq'.get?_take] at hv
      apply eq_of_forall_ge_iff hv
    simp [Seq'.get?_take]
    conv =>
      enter [m, 1, hm]
      tactic =>
        apply eq_false
        rcases Seq'.ge_stable _ (le_of_lt hm) hp with ⟨q, hq⟩
        simp [hq]
    simp [imp_false]
  have hv₂ := congr_arg ((↑) : ℤ → K) (((of v).take n).determinant p)
  simp [hv₁, hp₂] at hv₂
  simp [convergents, FCF.eval, Rat.mkRat_eq_div, ← hv₂]
  field_simp
  ring
#align generalized_continued_fraction.sub_convergents_eq CF.sub_convergents_eq

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`. -/
theorem abs_sub_convergents_le (hv : ¬(of v).s.TerminatedAt n) :
    |v - (of v).convergents n| ≤
      ((↑(take n (of v)).denominator : K) * ↑(take (n + 1) (of v)).denominator)⁻¹ := by
  cases n using Nat.casesAuxOn with
  | zero =>
    simp [TerminatedAt, Seq'.get?_zero] at hv
    simp [convergents, CF.take, Seq'.take, hv, abs_eq_self.mpr (fract_nonneg v)]
    rw [le_inv]
    · apply Nat.floor_le; simp
    · rw [lt_iff_le_and_ne, ne_comm]; simp [hv]
    · simp [Nat.floor_pos, one_le_inv_iff]
      rw [lt_iff_le_and_ne, ne_comm]; simp [hv, le_of_lt (fract_lt_one v)]
  | succ n =>
    obtain ⟨w, hw⟩ : ∃ w, get? (fractParts v) (n + 1) = some w
    · simpa [of_terminatedAt_iff_fractParts_terminatedAt, not_terminatedAt_iff (s := fractParts v),
        Option.isSome_iff_exists] using hv
    obtain ⟨n₂, hn₂⟩ : ∃ n₂, get? (of v).s (n + 1) = some n₂
    · simpa [not_terminatedAt_iff, Option.isSome_iff_exists] using hv
    obtain ⟨n₁, hn₁⟩ : ∃ n₁, get? (of v).s n = some n₁ :=
      ge_stable _ (le_of_lt n.lt_succ_self) hn₂
    simp [sub_convergents_eq hw, abs_div, abs_mul]
    apply inv_le_inv_of_le
    · simp
    · refine le_trans ?_ (le_abs_self _)
      simp [CF.take, Seq'.take_succ, hn₁, hn₂, - of_s_succ, of_s_le_inv_fractParts hn₂ hw]
#align generalized_continued_fraction.abs_sub_convergents_le CF.abs_sub_convergents_le

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`GCF.abs_sub_convergents_le`, but sometimes it is easier to apply and sufficient for one's use case.
 -/
theorem abs_sub_convergents_le' {m : ℕ+} (hm : get? (of v).s n = m) :
    |v - (of v).convergents n| ≤
      ((↑m : K) * ↑(take n (of v)).denominator * ↑(take n (of v)).denominator)⁻¹ := by
  refine le_trans (abs_sub_convergents_le ?_) ?_
  · simp [TerminatedAt, hm]
  · simp [CF.take, Seq'.take_succ, hm, - mul_inv_rev, inv_le_inv]
    rw [mul_comm (a := (↑m : K)), mul_assoc]; simp
    norm_cast; apply FCF.mul_denom_le_concat_denom
#align generalized_continued_fraction.abs_sub_convergents_le' CF.abs_sub_convergents_le'

end CF

end ErrorTerm
