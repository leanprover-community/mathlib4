import Mathlib.Tactic.Ring

local instance [CommSemiring α] : CoeTail Nat α where
  coe n := n.cast

example (x y : ℕ) : x + y = y + x := by ring
example (x y : ℕ) : x + y + y = 2 * y + x := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example {α} [CommRing α] (x y : α) : x + y + y - x = 2 * y := by ring
example {α} [CommSemiring α] (x y : α) : (x + y)^2 = x^2 + 2 • x * y + y^2 := by ring

example (x y : ℕ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
-- example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example {α} [CommSemiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by ring
example (n : ℕ) : (n / 2) + (n / 2) = 2 * (n / 2) := by ring
example {α} [LinearOrderedField α] (a b c : α) :
  a * (-c / b) * (-c / b) + -c + c = a * (c / b * (c / b)) := by ring
example {α} [LinearOrderedField α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example {α} [CommSemiring α] (x : α) : x ^ (2 + 2) = x^4 := by ring
example {α} [CommSemiring α] (x : α) : x ^ (2 + 2) = x^4 := by ring_nf
-- example {α} [CommRing α] (x : α) : x ^ (2 : ℤ)  = x * x := by ring
-- example {α} [LinearOrderedField α] (a b c : α) :
--   b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
-- example {α} [LinearOrderedField α] (a b c : α) :
--   b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring
example {α} [CommSemiring α] (x y z : α) (n : ℕ) :
  (x + y) * (z * (y * y) + (x * x ^ n + (1 + ↑n) * x ^ n * y)) =
  x * (x * x ^ n) + ((2 + ↑n) * (x * x ^ n) * y +
    (x * z + (z * y + (1 + ↑n) * x ^ n)) * (y * y)) := by ring
example {α} [CommRing α] (a b c d e : α) :
  (-(a * b) + c + d) * e = (c + (d + -a * b)) * e := by ring
example (a n s: ℕ) : a * (n - s) = (n - s) * a := by ring

section Rat

variable [Field α]

example (x : ℚ) : x / 2 + x / 2 = x := by ring
example (x : α) : x / 2 = x / 2 := by ring
example (x : α) : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by ring1
example (x : α) : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by ring1
example (x y : α): x * y⁻¹ = (y * x⁻¹)⁻¹ := by ring1
example (x y : α): x * y⁻¹ = y⁻¹ * x := by ring1
example (x y z : α): (x * (y * z)⁻¹)⁻¹ = x⁻¹ * y * z := by ring1
example (x : α) : x = x⁻¹⁻¹ := by ring1
example (x : α) : x = x⁻¹⁻¹⁻¹⁻¹ := by ring1
example (x y : α) : y⁻¹⁻¹⁻¹ * x⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹ = x⁻¹⁻¹⁻¹⁻¹ * y⁻¹ := by ring1

example (x y : α) : (x^2 * y)⁻¹ = (y * x^2)⁻¹ := by ring1
example (x y : α) : (x^2)⁻¹ * y = (y⁻¹ * x^2)⁻¹ := by ring1
example (x y : α) : (x^2)⁻¹ / y = (y * x^2)⁻¹ := by ring1
example (x y : α) : (x⁻¹^2)⁻¹ / y = y⁻¹ * x^2 := by ring1
example (x y : α) : (x + y)⁻¹ = (x + y)⁻¹⁻¹⁻¹ := by ring1
example (x y : α) : (x + y)⁻¹ = (y + x)⁻¹⁻¹⁻¹ := by ring1
example (x y : α) : (x * y)⁻¹ = (y * x)⁻¹⁻¹⁻¹ := by ring1
example (x y : α) : (x - x + y)⁻¹ = (x + y⁻¹ - x)⁻¹⁻¹ := by ring1
example (x y : α) : 3 / (x - x + y)⁻¹ = 3 * (x + y⁻¹ - x)⁻¹ := by ring1

--!! did mathlib3 have these?
example (y : α) [Invertible y] : y⁻¹ * y = 1 := by ring1
example (y : αˣ) : y⁻¹ * y = 1 := by ring1
example (y : α) (_ : y ≠ 0) : y⁻¹ * y = 1 := by ring1

--!! We don't necessarily have x * x⁻¹ = 1, but we should have that x^n * x⁻¹^m = "x ^ (n - m)"
--!! for n ≠ m (represented in terms of whichever of x or x⁻¹ we need).
--!! Also, what's the mathlib form of "χ[αˣ](x)" (or "Boole (x ≠ 0)", or "if x = 0 then 0 else 1")? --!! Not essential, but it would be useful to normalize to that.
example (x : α) : x * x⁻¹ * x = x := by ring1

variable [CharZero α]

example (x : α) : x / 2 = x / 2 := by ring
example (x : α) : (x : α) = x * (5/3)*(3/5) := by ring1
example : (1 + 1)⁻¹ = (2⁻¹ : α) := by ring1

end Rat

example (A : ℕ) : (2 * A) ^ 2 = (2 * A) ^ 2 := by ring

-- example (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
--   x / (y / z) + y ⁻¹ + 1 / (y * -x) = -1/ (x * y) + (x * z + 1) / y :=
-- begin
--   field_simp,
--   ring
-- end

-- example (a b c d x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
--   a + b / x - c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x - c) / x) :=
-- begin
--   field_simp,
--   ring
-- end

example : (876544 : ℤ) * -1 + (1000000 - 123456) = 0 := by ring

-- example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
--   2 * x ^ 3 * 2 / (24 * x) = x ^ 2 / 6 :=
-- begin
--   field_simp,
--   ring
-- end

example (A B : ℕ) (H : B * A = 2) : A * B = 2 := by ring_nf at H ⊢; exact H

example (f : ℕ → ℕ) :
  2 + f (2 * f 3 * f 3) + f 3 = 1 + f (f 3 ^ 2 + f 3 * f 3) + 1 + f (2 + 1) := by ring_nf

example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!

-- Example with ring discharging the goal
example : 22 + 7 * 4 + 3 * 8 = 0 + 7 * 4 + 46 := by
  conv => ring
  trivial -- FIXME: not needed in lean 3

-- Example with ring failing to discharge, to normalizing the goal
example : (22 + 7 * 4 + 3 * 8 = 0 + 7 * 4 + 47) = (74 = 75) := by
  conv => ring
  trivial

-- Example with ring discharging the goal
example (x : ℕ) : 22 + 7 * x + 3 * 8 = 0 + 7 * x + 46 := by
  conv => ring
  trivial

-- Example with ring failing to discharge, to normalizing the goal
example (x : ℕ) : (22 + 7 * x + 3 * 8 = 0 + 7 * x + 46 + 1)
                    = (7 * x + 46 = 7 * x + 47) := by
  conv => ring
  trivial
