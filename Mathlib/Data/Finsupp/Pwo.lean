/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module data.finsupp.pwo
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Order
import Mathbin.Order.WellFoundedSet

/-!
# Partial well ordering on finsupps

This file contains the fact that finitely supported functions from a fintype are
partially well ordered when the codomain is a linear order that is well ordered.
It is in a separate file for now so as to not add imports to the file `order.well_founded_set`.

## Main statements

* `finsupp.is_pwo` - finitely supported functions from a fintype are partially well ordered when
  the codomain is a linear order that is well ordered

## Tags

Dickson, order, partial well order
-/


/-- A version of **Dickson's lemma** any subset of functions `σ →₀ α` is partially well
ordered, when `σ` is `finite` and `α` is a linear well order.
This version uses finsupps on a finite type as it is intended for use with `mv_power_series`.
-/
theorem Finsupp.isPwo {α σ : Type _} [Zero α] [LinearOrder α] [IsWellOrder α (· < ·)] [Finite σ]
    (S : Set (σ →₀ α)) : S.IsPwo :=
  Finsupp.equivFunOnFinite.symm_image_image S ▸
    Set.PartiallyWellOrderedOn.image_of_monotone_on (Pi.isPwo _) fun a b ha hb => id
#align finsupp.is_pwo Finsupp.isPwo

