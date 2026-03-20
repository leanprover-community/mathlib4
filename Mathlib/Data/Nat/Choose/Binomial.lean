/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Binomial

This file defines the binomial coefficient `Nat.binom a b`, which returns the coefficient of
`x^a y^b` in the expansion of `(x + y)^(a + b)`.

Note the similarity to `Nat.choose`. However, `Nat.binom` may be easier to use in some contexts,
as it does not require the user to prove `b ≤ a + b` in order to prove positivity.

## Main declarations

- `Nat.binomial`: the multinomial coefficient


-/

open Finset
open scoped Nat

namespace Nat

def binom : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ => 1
  | a + 1, b + 1 => choose (a + 1) b + choose a (b + 1)


-- TODO: uncomment
-- variable (a b : ℕ)


lemma binom_eq_choose (a b : ℕ) : binom a b = Nat.choose (a + b) a := by
  sorry

@[simp]
lemma binom_zero_right (a : ℕ) : binom a 0 = 1 := by
  simp [binom_eq_choose]

@[simp]
lemma binom_zero_left (b : ℕ) : binom 0 b = 1 := by
  simp [binom_eq_choose]

@[simp]
lemma binom_one_right (a : ℕ) : binom a 1 = a + 1 := by
  simp [binom_eq_choose]

@[simp]
lemma binom_one_left (b : ℕ) : binom 1 b = 1 + b := by
  simp [binom_eq_choose]

lemma binom_succ_succ (a b : ℕ) :
    binom (succ a) (succ b) = binom a (succ b) + binom (succ a) b := by
  simp [binom_eq_choose, Nat.choose_succ_succ]
  sorry

lemma binom_succ_succ' (a b : ℕ) :
    binom (a + 1) (b + 1) = binom a (b + 1) + binom (a + 1) b := by
  convert binom_succ_succ a b

lemma binom_symm (a b : ℕ) : binom a b = binom b a := by
  simpa [binom_eq_choose, add_comm] using choose_symm_add

theorem binom_pos (a b : ℕ) : 0 < binom a b := sorry

theorem binom_eq_factorial_div_factorial (a b : ℕ) : binom a b =
    (a + b)! / (a ! * b !) := by simp [binom_eq_choose, choose_eq_factorial_div_factorial]

theorem binom_eq_multinomial (a b : ℕ) :
    binom a b = Nat.multinomial (Finset.univ) ![a, b] := by
  simp [multinomial_univ_two, binom_eq_choose, choose_eq_factorial_div_factorial]

section PositivityExtension

open Lean Meta Mathlib Meta Positivity Qq in
/-- The `positivity` extension which identifies expressions of the form `binom a b`. -/
@[positivity binom (_ : ℕ) (_ : ℕ)]
def evalBinom : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(binom $a $b) =>
    assertInstancesCommute
    return .positive q(binom_pos $a $b)
  | _, _, _ => throwError "not binom"

end PositivityExtension

end Nat

-- TODO: Lemmas analogous to those in Mathlib/Data/Nat/Choose/Basic.lean
