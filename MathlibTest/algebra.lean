import Mathlib.Tactic.Algebra

axiom sorryAlgebraTest {P : Prop} : P

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  match_scalars_alg

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  algebra

-- weird behaviour, would hope both sides turn into zsmul
example (x : ℚ) (n : ℕ) : n • x + x = (n : ℤ) • x + x := by
  algebra_nf
  exact sorryAlgebraTest


example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra

example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra_nf

example {R A : Type*} {a b : R} [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A) :
    (a + b) • (x + y) = b • x + a • (x + y) + b • y := by
  -- ring does nothing
  try ring_nf
  algebra

example {R A : Type*} {a b : R} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    (a - b) • (x + y) = - b • x + a • (x + y) - b • y := by
  -- ring does nothing
  ring_nf
  algebra

example {x : ℚ} {y : ℤ} : y • x + (1:ℤ) • x = (1 + y) • x := by
  algebra

example (x : ℚ) :  x + x = (2 : ℤ) • x := by
  algebra

example (x : ℚ) : x = 1 := by
  algebra_nf with ℕ
  exact sorryAlgebraTest

example (x y : ℚ) : x + y  = y + x := by
  algebra

example (x y : ℚ) : x + y*x + x + y  = (x + x) + (x*y + y) := by
  algebra

example (x : ℚ) : x + x + x  = 3 * x := by
  algebra

example (x : ℚ) : (x + x) + (x + x)  = x + x + x + x := by
  algebra

example (x y : ℚ) : x + (y)*(x+y) = 0 := by
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : x + (x)*(x + -y) = 0 := by
  algebra_nf with ℤ
  exact sorryAlgebraTest


example (x y : ℚ) : (x * x + x * y) + (x * y + y * y) = 0 := by
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  algebra

-- Handle negative integer constants
example (x y : ℚ) : (x + (-3) * y)*(x+y) = x*x + (-2) * x * y + (-3) * y^2 := by
  algebra with ℤ

example (x y : ℚ) : (x+y)*x = 1 := by
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : (x+y)*y  = 1 := by
  algebra_nf with ℕ
  exact sorryAlgebraTest


example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra

example (x : ℚ) (hx : x = 0) : (x+1)^10 = 1 := by
  algebra_nf
  guard_target = 1 + x * 10 + x ^ 2 * 45 + x ^ 3 * 120 + x ^ 4 * 210 + x ^ 5 * 252 + x ^ 6 * 210 + x ^ 7 * 120 + x ^ 8 * 45 +
      x ^ 9 * 10 +
    x ^ 10 = 1
  simp [hx]

example {a b : ℤ} (x y : ℚ) (ha : a = 2) : (a + b) • (x + y) = b • x + (2:ℤ) • (x + y) + b • y := by
  match_scalars_alg with ℤ
  · grind
  · grind

example {a b : ℤ} (x y : ℚ) : (a - b) • (x + y) = 0 := by
  algebra_nf
  exact sorryAlgebraTest


example (x y : ℚ) (a : ℤ) (h : 2 * a = 3) : (x + a • y)^2 = x^2 + 3 * x*y + a^2 • y^2 := by
  grind


example : 2 = 1 := by
  match_scalars_alg with ℕ
  exact sorryAlgebraTest

-- #lint

example (x : ℚ) (n : ℕ) : (x + 2) ^ (2 * n+1) = ((x+2)^n)^2 * (x+2) := by
  algebra

example (x : ℚ) (n : ℕ) : (x^n + 1)^2 = 0 := by
  algebra_nf
  exact sorryAlgebraTest
