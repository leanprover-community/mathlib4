/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module data.int.cast.field
! leanprover-community/mathlib commit ee0c179cd3c8a45aa5bffbf1b41d8dbede452865
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Cast of integers into fields

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

 * `Int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/


namespace Int

open Nat

variable {α : Type _}

/-- Auxiliary lemma for norm_cast to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `Field` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
theorem cast_neg_natCast {R} [Field R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp
#align int.cast_neg_nat_cast Int.cast_neg_natCast

@[simp]
theorem cast_div [Field α] {m n : ℤ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
    ((m / n : ℤ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by
    rintro rfl
    simp at n_nonzero
  rw [Int.mul_ediv_cancel_left _ this, Int.cast_mul, mul_div_cancel_left _ n_nonzero]
#align int.cast_div Int.cast_div

end Int
