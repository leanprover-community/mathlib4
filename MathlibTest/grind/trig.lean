import Mathlib

set_option grind.warning false

open Real

grind_pattern cos_sq_add_sin_sq => cos x
grind_pattern cos_sq_add_sin_sq => sin x

-- Whenever `grind` sees `cos` or `sin`, it adds `(cos x)^2 + (sin x)^2 = 1` to the blackboard.
-- That's a polynomial, so it is sent to the Grobner basis module.
-- And we can prove equalities modulo that relation!
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind +ring

-- `grind` notices that the two arguments of `f` are equal,
-- and hence the function applications are too.
example (f : ℝ → ℕ) : f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind +ring

-- After that, we can use basic modularity conditions:
-- this reduces to `4 * x ≠ 2 + x` for some `x : ℕ`
example (f : ℝ → ℕ) : 4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind +ring

-- A bit of case splitting is also fine.
-- If `max = 3`, then `f _ = 0`, and we're done.
-- Otherwise, the previous argument applies.
example (f : ℝ → ℕ) : max 3 (4 * f ((cos x + sin x)^2)) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind +ring
