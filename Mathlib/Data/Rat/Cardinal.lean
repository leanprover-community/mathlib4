/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Floris Van Doorn
-/
module

public import Mathlib.Data.Rat.Init
public import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Encodable
import Mathlib.Init
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

public section

assert_not_exists Module Field

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
