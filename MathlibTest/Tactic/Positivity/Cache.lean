import Mathlib.Tactic.Positivity

/-! # Tests for the `positivity` cache -/

namespace Cache

set_option maxHeartbeats 700

example {x : ℤ} (hx : 0 ≤ x)
    : 0 ≤ ((((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x))))
        + (((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x)))))
  := by positivity

example {x : ℤ} (hx : 0 ≤ x)
    : 0 ≤ x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
        + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
  := by positivity

end Cache
