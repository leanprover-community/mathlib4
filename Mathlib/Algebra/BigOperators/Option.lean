/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module algebra.big_operators.option
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Option

/-!
# Lemmas about products and sums over finite sets in `option α`

In this file we prove formulas for products and sums over `finset.insert_none s` and
`finset.erase_none s`.
-/


open BigOperators

open Function

namespace Finset

variable {α M : Type _} [CommMonoid M]

@[simp, to_additive]
theorem prod_insert_none (f : Option α → M) (s : Finset α) :
    (∏ x in s.insertNone, f x) = f none * ∏ x in s, f (some x) := by simp [insert_none]
#align finset.prod_insert_none Finset.prod_insert_none

@[to_additive]
theorem prod_erase_none (f : α → M) (s : Finset (Option α)) :
    (∏ x in s.eraseNone, f x) = ∏ x in s, Option.elim' 1 f x := by
  classical calc
      (∏ x in s.erase_none, f x) = ∏ x in s.erase_none.map embedding.some, Option.elim' 1 f x :=
        (Prod_map s.erase_none embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x in s.erase none, Option.elim' 1 f x := by rw [map_some_erase_none]
      _ = ∏ x in s, Option.elim' 1 f x := prod_erase _ rfl
      
#align finset.prod_erase_none Finset.prod_erase_none

end Finset

