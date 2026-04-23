/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.Card
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Finite monoids are Dedekind-finite
-/

@[expose] public section

instance (M) [Monoid M] [Finite M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm {a b} hab := by
    have ⟨c, hbc⟩ := Finite.surjective_of_injective (isLeftRegular_of_mul_eq_one hab) 1
    rwa [left_inv_eq_right_inv hab hbc]
