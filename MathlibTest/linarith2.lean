import Mathlib.Tactic.Linarith.Frontend2

/-! # Tests for the `linarith?` self-replacing tactic -/

example {a b : ℚ} (h : a + b ≤ 0) : a + b ≤ 0 := by linarith?

example {a b : ℚ} (h : a ≤ 0) (h' : b ≤ 0) : a + b ≤ 0 := by linarith?

example {x y z : ℚ} (h1 : 4 * x + y + 3 * z ≤ 25) (h2 : -x + 2 * y + z = 3)
    (h3 : 5 * x + 7 * z = 43) :
    x ≤ 4 := by
  linarith?
  -- linear_combination (7 / 19 * h1 - 7 / 38 * h2 - 5 / 38 * h3)

example {x y z : ℚ} (h1 : 4 * x + y + 3 * z ≤ 25) (h2 : 3 = -x + 2 * y + z)
    (h3 : 5 * x + 7 * z = 43) :
    x ≤ 4 := by
  linarith?


/--
error: linarith's equality proofs cannot be translated to linear_combination proofs; use polyrith instead
-/
#guard_msgs in
example {a b : ℚ} (h1 : a = 1) (h2 : a + b = 2) : b = 1 := by linarith?

/-- error: linarith? failed to find a contradiction -/
#guard_msgs in
example {a : ℚ} (h : a < 1) : a < 0 := by linarith? -- FIXME bug

-- example {a : ℚ} (h : a < 0) : a < 1 := by linarith? -- FIXME bug
