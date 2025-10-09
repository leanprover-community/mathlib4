import Mathlib.Tactic.Algebra

axiom sorryAlgebraTest {P : Prop} : P

example {x : ℚ} {y : ℤ} : y • x + (1:ℤ) • x = (1 + y) • x := by
  algebra

-- why doesn't match_expr match on the HSMul.hSmul expression?????
example (x : ℚ) :  x + x = (2 : ℤ) • x := by
  algebra
  -- match_scalars <;> simp

example (x : ℚ) : x = 1 := by
  algebra_nf with ℕ
  exact sorryAlgebraTest

example (x y : ℚ) : x + y  = y + x := by
  algebra

example (x y : ℚ) : x + y*x + x + y  = (x + x) + (x*y + y) := by
  algebra

-- BUG: ExProd.one doesn't match with the empty product in sums.
example (x : ℚ) : x + x + x  = 3 * x := by
  algebra

example (x : ℚ) : (x + x) + (x + x)  = x + x + x + x := by
  algebra

example (x y : ℚ) : x + (y)*(x+y) = 0 := by
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : x + (x)*(x + -y) = 0 := by
  -- NOTE: it can only handle negation if the base ring can.
  algebra_nf with ℤ
  exact sorryAlgebraTest


example (x y : ℚ) : (x * x + x * y) + (x * y + y * y) = 0 := by
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra

-- Handle negative integer constants
example (x y : ℚ) : (x + (-3) * y)*(x+y) = x*x + (-2) * x * y + (-3) * y^2 := by
  algebra with ℤ

example (x y : ℚ) : (x+y)*x = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra_nf
  exact sorryAlgebraTest

example (x y : ℚ) : (x+y)*y  = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra_nf with ℕ
  exact sorryAlgebraTest


example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra

example (x : ℚ) (hx : x = 0) : (x+1)^10 = 1 := by
  algebra_nf
  simp [hx]

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

--TODO: this is broken; should cast the natural smul into integer smul.
example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  match_scalars_alg with ℤ

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  algebra

-- weird behaviour
example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  algebra_nf
  exact sorryAlgebraTest


example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra_nf
