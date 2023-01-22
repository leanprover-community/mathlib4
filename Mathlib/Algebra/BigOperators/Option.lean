/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module algebra.big_operators.option
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Option

/-!
# Lemmas about products and sums over finite sets in `Option α`

In this file we prove formulas for products and sums over `Finset.insertNone s` and
`Finset.eraseNone s`.
-/

-- Porting note: big operators are currently global
--open BigOperators

open Function

namespace Finset

variable {α M : Type _} [CommMonoid M]

@[to_additive (attr := simp)]
theorem prod_insertNone (f : Option α → M) (s : Finset α) :
    (∏ x in insertNone s, f x) = f none * ∏ x in s, f (some x) := by simp [insertNone]
#align finset.prod_insert_none Finset.prod_insertNone
#align finset.sum_insert_none Finset.sum_insertNone

@[to_additive]
theorem prod_eraseNone (f : α → M) (s : Finset (Option α)) :
    (∏ x in eraseNone s, f x) = ∏ x in s, Option.elim' 1 f x := by
  classical calc
      (∏ x in eraseNone s, f x) = ∏ x in (eraseNone s).map Embedding.some, Option.elim' 1 f x :=
        (prod_map (eraseNone s) Embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x in s.erase none, Option.elim' 1 f x := by rw [map_some_eraseNone]
      _ = ∏ x in s, Option.elim' 1 f x := prod_erase _ rfl
#align finset.prod_erase_none Finset.prod_eraseNone
#align finset.sum_erase_none Finset.sum_eraseNone

end Finset
