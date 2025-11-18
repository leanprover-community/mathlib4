import Mathlib

set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

-- Verify that basic functionality of `sineQuaNon` still works after importing Mathlib.
example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  fail_if_success grind
  grind +suggestions

-- Verify that `sineQuaNon` finds Mathlib theorems, too.
open Real
-- This is exactly `rpowIntegrand₀₁_nonneg`
example (hp : 0 < p) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ rpowIntegrand₀₁ p t x := by
  fail_if_success grind
  grind +suggestions
