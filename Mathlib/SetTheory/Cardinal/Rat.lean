/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Floris Van Doorn
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Data.Rat.Encodable
public import Mathlib.SetTheory.Cardinal.Basic

import Mathlib.Algebra.Ring.Rat

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

public section

assert_not_exists Module Field

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
