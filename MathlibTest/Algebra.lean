import Mathlib.Tactic.Algebra.Basic

axiom sorryAlgebraTest {P : Prop} : P

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  algebra

example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra

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

example (x y : ℚ) : x + y  = y + x := by
  algebra

example (x y : ℚ) : x + y*x + x + y  = (x + x) + (x*y + y) := by
  algebra

example (x : ℚ) : x + x + x  = 3 * x := by
  algebra

example (x : ℚ) : (x + x) + (x + x)  = x + x + x + x := by
  algebra

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  algebra

-- Handle negative integer constants
example (x y : ℚ) : (x + (-3) * y)*(x+y) = x*x + (-2) * x * y + (-3) * y^2 := by
  algebra with ℤ

example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra

example (x : ℚ) (n : ℕ) : (x + 2) ^ (2 * n+1) = ((x+2)^n)^2 * (x+2) := by
  algebra

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

-- Test with Algebra over ℚ
example {A : Type*} [CommRing A] [Algebra ℚ A] (x y : A) :
    (1/2 : ℚ) • (x + y) = (1/2 : ℚ) • x + (1/2 : ℚ) • y := by
  algebra

example {A : Type*} [CommRing A] [Algebra ℚ A] (x : A) :
    (3/4 : ℚ) • x + (1/4 : ℚ) • x = x := by
  algebra with ℚ
