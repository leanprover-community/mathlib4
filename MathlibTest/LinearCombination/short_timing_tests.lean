import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Notation
import Mathlib.Util.Time
import Mathlib.Tactic.Abel

axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.linearOrderedField : LinearOrderedField ℝ

#time
example {u v x y A B : ℝ} (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B := by
  linear_combination v * h2 + v * h3 + v * h4 + u * h5 + (v + B) * h8 + 2 * B * h9

#time
example {u v x y A B : ℝ} (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B := by
  nlinarith

#time
example (u v x y A B : ℚ)
    (h1 : u < A)
    (h2 : v < A)
    (h5 : A ≤ A * B)
    (h6 : A * u < A)
    (h7 : 0 ≤ (B - 1) * (A - u))
    (h8 : 0 ≤ (B - 1) * (A - v))
    (h9 : x * v ≤ B * v)
    (h10 : y * u ≤ B * u)
    (h11 : u * v ≤ u * A) :
    u * y + v * x + u * v < 3 * A * B := by
  linarith

#time
example (u v x y A B : ℚ)
    (h1 : u < A)
    (h2 : v < A)
    (h5 : A ≤ A * B)
    (h6 : A * u < A)
    (h7 : 0 ≤ (B - 1) * (A - u))
    (h8 : 0 ≤ (B - 1) * (A - v))
    (h9 : x * v ≤ B * v)
    (h10 : y * u ≤ B * u)
    (h11 : u * v ≤ u * A) :
    u * y + v * x + u * v < 3 * A * B := by
  linear_combination h1 + h2 + h5 + h6 + h7 + h8 + h9 + h10 + h11

#time
example {x y z : ℚ} (h1 : 4 * x + y + 3 * z ≤ 25) (h2 : -x + 2 * y + z = 3)
    (h3 : 5 * x + 7 * z = 43) :
    x < 4 := by
  linarith

#time
example {x y z : ℚ} (h1 : 4 * x + y + 3 * z ≤ 25) (h2 : -x + 2 * y + z = 3)
    (h3 : 5 * x + 7 * z = 43) :
    x < 4 := by
  linear_combination (14 * h1 - 7 * h2 - 5 * h3) / 38

count_heartbeats in
example {a b c d e : ℚ}
    (h1 : 3 * a + 4 * b - 2 * c + d = 15)
    (h2 : a + 2 * b + c - 2 * d + 2 * e = 3)
    (h3 : 5 * a + 5 * b - c + d + 4 * e = 31)
    (h4 : 8 * a + b - c - 2 * d + 2 * e = 8)
    (h5 : 1 - 2 * b + 3 * c - 4 * d + 5 * e = -4) :
    a = 1 := by
  linarith

count_heartbeats in
example {a b c d e : ℚ}
    (h1 : 3 * a + 4 * b - 2 * c + d = 15)
    (h2 : a + 2 * b + c - 2 * d + 2 * e = 3)
    (h3 : 5 * a + 5 * b - c + d + 4 * e = 31)
    (h4 : 8 * a + b - c - 2 * d + 2 * e = 8)
    (h5 : 1 - 2 * b + 3 * c - 4 * d + 5 * e = -4) :
    a = 1 := by
  linear_combination (-155 * h1 + 68 * h2 + 49 * h3 + 59 * h4 - 90 * h5) / 320

/-! ### (a:ℚ) ≤ b → 0 ≤ b - a -/

set_option maxHeartbeats 150 in
example {a b : ℚ} (h : a ≤ b) : 0 ≤ b - a := by
  linear_combination h

set_option maxHeartbeats 180 in
example {a b : ℚ} (h : a ≤ b) : 0 ≤ b - a := sub_nonneg.mpr h

set_option maxHeartbeats 610 in
example {a b : ℚ} (h : a = b) : 0 = b - a := by linarith

/-! ### (a:ℚ) + 1 ≤ b → 0 ≤ b - a -/

set_option maxHeartbeats 250 in
example {a b : ℚ} (h : a + 1 ≤ b) : 0 ≤ b - a := by
  linear_combination h

set_option maxHeartbeats 850 in
example {a b : ℚ} (h : a + 1 ≤ b) : 0 ≤ b - a := by
  linarith

/-! ### (a:ℝ) + 1 ≤ b → 0 ≤ b - a -/

count_heartbeats in
example {a b : ℝ} (h : a + 1 ≤ b) : 0 ≤ b - a := by
  linear_combination h

count_heartbeats in
example {a b : ℝ} (h : a + 1 ≤ b) : 0 ≤ b - a := by
  linarith

/-! ### (a:ℝ) + 1 ≤ b → 0 ≤ b - a -/

#time
example {a b : ℝ} (h : a + 1 ≤ b) : 0 ≤ b - a := by
  linear_combination h

#time
example {a b : ℝ} (h : a + 1 ≤ b) : 0 ≤ b - a := by
  linarith

/-! ### (a:ℚ) + 1.5 ≤ b → 0 ≤ b - a -/

set_option maxHeartbeats 500 in
example {a b : ℚ} (h : a + 1.5 ≤ b) : 0 ≤ b - a := by
  linear_combination h

-- example {a b : ℚ} (h : a + 1.5 ≤ b) : 0 ≤ b - a := by
--   linarith -- bug?

/-! ### more examples -/

set_option maxHeartbeats 1200 in
example {a1 a2 a3 a4 a5 a6 a7 : ℚ}
    (h1 : a1 ≤ 1)
    (h2 : a1 + a2 = 2)
    (h3 : a2 + a3 = 2)
    (h4 : a3 + a4 = 2)
    (h5 : a4 + a5 = 2)
    (h6 : a5 + a6 = 2)
    (h7 : a6 + a7 = 2) :
    a7 ≤ 1 := by
  linarith

set_option maxHeartbeats 1200 in
example {a1 a2 a3 a4 a5 a6 a7 : ℚ}
    (h7 : a6 + a7 = 2)
    (h6 : a5 + a6 = 2)
    (h5 : a4 + a5 = 2)
    (h4 : a3 + a4 = 2)
    (h3 : a2 + a3 = 2)
    (h2 : a1 + a2 = 2)
    (h1 : a1 ≤ 1) :
    a7 ≤ 1 := by
  linarith

set_option maxHeartbeats 500 in
example {a1 a2 a3 a4 a5 a6 a7 : ℚ}
    (h7 : a6 + a7 = 2)
    (h6 : a5 + a6 = 2)
    (h5 : a4 + a5 = 2)
    (h4 : a3 + a4 = 2)
    (h3 : a2 + a3 = 2)
    (h2 : a1 + a2 = 2)
    (h1 : a1 ≤ 1) :
    a7 ≤ 1 := by
  linear_combination h7 - h6 + h5 - h4 + h3 - h2 + h1
