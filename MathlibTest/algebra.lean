import Mathlib.Tactic.Algebra

axiom sorryAlgebraTest {P : Prop} : P

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  match_scalars_alg

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  algebra

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x : ℚ) (n : ℕ) : n • x + x = (n : ℤ) • x + x := by
  algebra_nf
  /- This behaviour is not desirable, it would be better if both sides were lifted to nsmul.
  We keep the test to document this behaviour. -/
  guard_target = (1 + n) • x = (1 + ↑n : ℤ) • x
  exact sorryAlgebraTest


example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra_nf

example {R A : Type*} {a b : R} [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A) :
    (a + b) • (x + y) = b • x + a • (x + y) + b • y := by
  algebra

example {R A : Type*} {a b : R} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    (a - b) • (x + y) = - b • x + a • (x + y) - b • y := by
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

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x y : ℚ) : x + (y)*(x+y) = 0 := by
  algebra_nf
  guard_target = x + x * y + y ^ 2 = 0
  exact sorryAlgebraTest

example (x y : ℚ) : x + (x)*(x + -y) = 0 := by
  algebra_nf with ℤ
  guard_target = x + -1 • (x * y) + x ^ 2 = 0
  exact sorryAlgebraTest

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x y : ℚ) : (x * x + x * y) + (x * y + y * y) = 0 := by
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  algebra

-- Handle negative integer constants
example (x y : ℚ) : (x + (-3) * y)*(x+y) = x*x + (-2) * x * y + (-3) * y^2 := by
  algebra with ℤ

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x y : ℚ) : (x+y)*x = 1 := by
  algebra_nf
  guard_target = x * y + x ^ 2 = 1
  exact sorryAlgebraTest

example (x y : ℚ) : (x+y)*y  = 1 := by
  algebra_nf with ℕ
  guard_target = x * y + y ^ 2 = 1
  exact sorryAlgebraTest


example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x : ℚ) (hx : x = 0) : (x+1)^10 = 1 := by
  algebra_nf
  -- TODO: decide if we want to turn nsmul/zsmul/qsmul with literals into multiplication.
  -- TODO: Now it's erroring because we're normalizing over ℚ and the target here is expressed in terms of ℤ. To avoid surprises here it might be helpful to convert to multiplying by a nat lit.
  guard_target =
      1 + 10 * x + 45 * x ^ 2 + 120 * x ^ 3 + 210 * x ^ 4 + 252 * x ^ 5 + 210 * x ^ 6 + 120 * x ^ 7 + 45 * x ^ 8 +
        10 * x ^ 9 + x ^ 10 = 1
  simp [hx]

example {a b : ℤ} (x y : ℚ) (ha : a = 2) : (a + b) • (x + y) = b • x + (2:ℤ) • (x + y) + b • y := by
  match_scalars_alg with ℤ
  · grind
  · grind

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example {a b : ℤ} (x y : ℚ) : (a - b) • (x + y) = 0 := by
  algebra_nf
  guard_target = (a - b) • x + (a - b) • y = 0
  exact sorryAlgebraTest


example (x y : ℚ) (a : ℤ) (h : 2 * a = 3) : (x + a • y)^2 = x^2 + 3 * x*y + a^2 • y^2 := by
  grind


example : 2 = 1 := by
  match_scalars_alg with ℕ
  exact sorryAlgebraTest

-- #lint

example (x : ℚ) (n : ℕ) : (x + 2) ^ (2 * n+1) = ((x+2)^n)^2 * (x+2) := by
  algebra

/--
info: Try this:
  algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x : ℚ) (n : ℕ) : (x^n - 1)^2 = 0 := by
  algebra_nf
  guard_target =  1 - 2 * x ^ n + x ^ (n * 2) = 0
  exact sorryAlgebraTest

-- Tests for rational constant handling (evalCast function)

-- Test positive rational constants
example (x : ℚ) : (1/2) * x = x * (1/2) := by
  algebra

example (x : ℚ) : (3/4) * x + (1/4) * x = x := by
  algebra with ℚ

example (x y : ℚ) : (1/2) * (x + y) = (1/2) * x + (1/2) * y := by
  algebra

example (x : ℚ) : (2/3) * x + (1/3) * x = x := by
  algebra with ℚ

-- Test negative rational constants
example (x : ℚ) : (-1/2) * x = -(x * (1/2)) := by
  algebra

example (x : ℚ) : (-3/4) * x + (3/4) * x = 0 := by
  algebra

example (x y : ℚ) : (-1/2) * x + (-1/2) * y = (-1/2) * (x + y) := by
  algebra

-- Test mixed rational and integer operations
example (x : ℚ) : 2 * x + (1/2) * x = (5/2) * x := by
  algebra

example (x : ℚ) : (1/2) * x - x = (-1/2) * x := by
  algebra

example (x : ℚ) : 3 * x - (1/4) * x = (11/4) * x := by
  algebra

-- Test rational constants in polynomial operations
example (x : ℚ) : ((1/2) * x + (1/3))^2 = (1/4) * x^2 + (1/3) * x + (1/9) := by
  algebra

example (x y : ℚ) : ((1/2) * x + (1/2) * y)^2 = (1/4) * (x^2 + 2 * x * y + y^2) := by
  algebra

example (x : ℚ) : (x + (2/3))^3 = x^3 + 2 * x^2 + (4/3) * x + (8/27) := by
  algebra

-- Test rational constants with scalar multiplication
example (x : ℚ) : (1/2 : ℚ) • x = (1/2) * x := by
  algebra

example (x : ℚ) : (3/4 : ℚ) • x + (1/4 : ℚ) • x = x := by
  algebra

-- Test algebra_nf with rational constants
example (x : ℚ) : (1/2) * x + (1/3) * x = 1 := by
  algebra_nf with ℚ
  guard_target = (5/6 : ℚ) • x = 1
  exact sorryAlgebraTest

example (x y : ℚ) : ((2/5) * x + (3/5) * y)^2 = 0 := by
  algebra_nf with ℚ
  guard_target = (12 / 25 : ℚ) • (x * y) + (4 / 25 : ℚ) • x ^ 2 + (9 / 25 : ℚ) • y ^ 2 = 0
  exact sorryAlgebraTest

-- Test with Algebra over ℚ
example {A : Type*} [CommRing A] [Algebra ℚ A] (x y : A) :
    (1/2 : ℚ) • (x + y) = (1/2 : ℚ) • x + (1/2 : ℚ) • y := by
  algebra

example {A : Type*} [CommRing A] [Algebra ℚ A] (x : A) :
    (3/4 : ℚ) • x + (1/4 : ℚ) • x = x := by
  algebra with ℚ
