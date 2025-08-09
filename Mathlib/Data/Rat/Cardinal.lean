/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Floris Van Doorn
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

assert_not_exists Module Field

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
