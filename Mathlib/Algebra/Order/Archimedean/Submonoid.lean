/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Submonoids of Archimedean monoids

This file defines the instances that show that the (mul-)Archimedean property is retained in a
submonoid of the ambient group.

## Main statements

* `SubmonoidClass.instMulArchimedean`: the submonoid (and similar subobjects) of a mul-Archimedean
  group retains the mul-Archimedean property when restricted to the submonoid.
* `AddSubmonoidClass.instArchimedean`: the additive submonoid (and similar subobjects) of an
  Archimedean additive group retains the Archimedean property when restricted to the additive
  submonoid.
-/

assert_not_exists Finset

@[to_additive]
instance SubmonoidClass.instMulArchimedean {M S : Type*} [SetLike S M]
    [CommMonoid M] [PartialOrder M]
    [SubmonoidClass S M] [MulArchimedean M] (H : S) : MulArchimedean H := by
  constructor
  rintro x _
  simp only [← Subtype.coe_lt_coe, OneMemClass.coe_one]
  exact MulArchimedean.arch x.val
