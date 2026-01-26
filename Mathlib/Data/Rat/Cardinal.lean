import Mathlib.SetTheory.Cardinal.Defs

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

public section

assert_not_exists Module Field

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
