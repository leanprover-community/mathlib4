
/-!
# Denumerability of ℚ

This file proves that ℚ is denumerable.

The fact that ℚ has cardinality ℵ₀ is proved in `Mathlib/Data/Rat/Cardinal.lean`
-/

@[expose] public section

assert_not_exists Module Field

namespace Rat

open Denumerable

/-- **Denumerability of the Rational Numbers** -/
instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ

end Rat
