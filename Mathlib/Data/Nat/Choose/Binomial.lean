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

-- TODO: uncomment
-- variable (a b : ℕ)

def binom (a b : ℕ) : ℕ := Nat.choose (a + b) a

@[simp]
lemma binom_eq_choose (a b : ℕ) : binom a b = Nat.choose (a + b) a := rfl

lemma binom_symm (a b : ℕ) : binom a b = binom b a := by
  simpa [add_comm] using choose_symm_add

theorem binom_pos (a b : ℕ) : 0 < binom a b := Nat.choose_pos (le_add_right a b)

theorem binom_eq_factorial_div_factorial (a b : ℕ) : binom a b =
    (a + b)! / (a ! * b !) := by simp [choose_eq_factorial_div_factorial]

theorem binom_eq_multinomial (a b : ℕ) :
    binom a b = Nat.multinomial (Finset.univ) ![a, b] := by
  simp [multinomial_univ_two]
  simp [choose_eq_factorial_div_factorial]

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
