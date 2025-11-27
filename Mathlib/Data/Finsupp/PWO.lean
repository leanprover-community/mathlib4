/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.Order.WellFoundedSet

/-!
# Partial well ordering on finsupps

This file contains the fact that finitely supported functions from a fintype are
partially well-ordered when the codomain is a linear order that is well ordered.
It is in a separate file for now so as to not add imports to the file `Order.WellFoundedSet`.

## Main statements

* `Finsupp.isPWO` - finitely supported functions from a fintype are partially well-ordered when
  the codomain is a linear order that is well ordered

## Tags

Dickson, order, partial well order
-/

@[expose] public section
/-- A version of **Dickson's lemma**: `σ →₀ α` is well-quasi-ordered when `σ` is `Finite` and `α` is
well-quasi-ordered.
This version uses finsupps on a finite type as it is intended for use with `MVPowerSeries`.
-/
instance Finsupp.wellQuasiOrderedLE {α σ : Type*} [Zero α] [Preorder α] [WellQuasiOrderedLE α]
    [Finite σ] : WellQuasiOrderedLE (σ →₀ α) :=
  orderIsoFunOnFinite.wellQuasiOrderedLE_iff.2 inferInstance

@[deprecated Set.isPWO_of_wellQuasiOrderedLE (since := "2025-11-12")]
theorem Finsupp.isPWO {α σ : Type*} [Zero α] [Preorder α] [WellQuasiOrderedLE α] [Finite σ]
    (S : Set (σ →₀ α)) : S.IsPWO :=
  Set.isPWO_of_wellQuasiOrderedLE S
