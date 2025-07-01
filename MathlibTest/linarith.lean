import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Oracle.FourierMotzkin
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Order.Interval.Finset.Nat

private axiom test_sorry : ∀ {α}, α
set_option linter.unusedVariables false
set_option autoImplicit false

open Lean.Elab.Tactic in
def testSorryTac : TacticM Unit := do
  let e ← getMainTarget
  let t ← `(test_sorry)
  closeMainGoalUsing `sorry fun _ _ => elabTerm t e

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (h : a < b) (w : b < a) : False := by
  linarith

example {α : Type} (_inst : (a : Prop) → Decidable a)
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α}
    (ha : a < 0)
    (hb : ¬b = 0)
    (hc' : c = 0)
    (h : (1 - a) * (b * b) ≤ 0)
    (hc : 0 ≤ 0)
    (w : -(a * -b * -b + b * -b + 0) = (1 - a) * (b * b))
    (h : (1 - a) * (b * b) ≤ 0) :
    0 < 1 - a := by
  linarith

example (e b c a v0 v1 : Rat) (h1 : v0 = 5 * a) (h2 : v1 = 3 * b) (h3 : v0 + v1 + c = 10) :
    v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  linarith

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (e b c a v0 v1 : α) (h1 : v0 = 5 * a) (h2 : v1 = 3 * b)
    (h3 : v0 + v1 + c = 10) : v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  linarith

example (h : (1 : ℤ) < 0) (g : ¬ (37 : ℤ) < 42) (_k : True) (l : (-7 : ℤ) < 5): (3 : ℤ) < 7 := by
  linarith [(rfl : 0 = 0)]

example (u v r s t : Rat) (h : 0 < u * (t * v + t * r + s)) : 0 < (t * (r + v) + s) * 3 * u := by
  linarith

example (A B : Rat) (h : 0 < A * B) : 0 < 8*A*B := by
  linarith

example (A B : Rat) (h : 0 < A * B) : 0 < A*8*B := by
  linarith

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (x : α) : 0 ≤ x := by
  have h : 0 ≤ x := test_sorry
  linarith

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (x : α) : 0 ≤ x := by
  have h : 0 ≤ x := test_sorry
  linarith [h]

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (u v r s t : α) (h : 0 < u * (t * v + t * r + s)) :
    0 < (t*(r + v) + s)*3*u := by linarith

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (A B : α) (h : 0 < A * B) : 0 < 8*A*B := by
  linarith

example (s : Set ℕ) (_h : s = ∅) : 0 ≤ 1 := by linarith

section cancel_denoms

example (A B : Rat) (h : 0 < A * B) : 0 < A*B/8 := by
  linarith

example (A B : Rat) (h : 0 < A * B) : 0 < A/8*B := by
  linarith

example (ε : Rat) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  linarith

example (x y z : Rat) (h1 : 2 * x < 3 * y) (h2 : -4 * x + z / 2 < 0)
    (h3 : 12 * y - z < 0) : False := by
  linarith

example (ε : Rat) (h1 : 0 < ε) : ε / 2 < ε := by linarith

example (ε : Rat) (h1 : 0 < ε) : ε / 3 + ε / 3 + ε / 3 = ε := by linarith

-- Make sure special case for division by 1 is handled:
example (x : Rat) (h : 0 < x) : 0 < x/1 := by linarith

-- Make sure can divide by -1
example (x : Rat) (h : x < 0) : 0 < x/(-1) := by linarith

example (x : Rat) (h : x < 0) : 0 < x/(-2) := by linarith

example (x : Rat) (h : x < 0) : 0 < x/(-4/5) := by linarith

example (x : Rat) (h : 0 < x) : 0 < x/2/3 := by linarith

example (x : Rat) (h : 0 < x) : 0 < x/(2/3) := by linarith

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example (a : K) (ha : 10 / (8 + 2) ≤ a) : 1 ≤ a := by linarith

example (a : K) (ha : 10 / 10 ^ 1 ≤ a) : 1 ≤ a := by linarith

example (a : K) (ha : 10⁻¹ * 10 ≤ a) : 1 ≤ a := by linarith

example (a : K) (ha : 1.0 ≤ a) : 1 ≤ a := by linarith

end cancel_denoms

example (a b c : Rat) (h2 : b + 2 > 3 + b) : False := by
  linarith (config := {discharger := do Lean.Elab.Tactic.evalTactic (←`(tactic| ring1))})

example (a b c : Rat) (h2 : b + 2 > 3 + b) : False := by
  linarith

-- We haven't implemented `restrict_type` yet.
-- example (a b c : ℚ) (x y : ℤ) (h1 : x ≤ 3*y) (h2 : b + 2 > 3 + b) : false :=
-- by linarith (restrict_type := ℚ)

example (g v V c h : Rat) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
    (h5 : 0 ≤ c) (h6 : c < 1) : v ≤ V := by
  linarith

example (x y z : ℤ) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) : False := by
  linarith

example (x y z : ℤ) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : x * y < 5) (h3 : 12 * y - 4 * z < 0) :
    False := by
  linarith

example (a b c : Rat) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  linarith

example (a b c : Rat) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  linarith

example (x y z : Rat) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3*y := by
  linarith

example (x y z : ℤ) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : x * y < 5) : ¬ 12*y - 4* z < 0 := by
  linarith

example (x y z : Rat) (hx : ¬ x > 3 * y) (h2 : ¬ y > 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  linarith

example (x y : Rat) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
    (h'' : (6 + 3 * y) * y ≥ 0) : False := by
  linarith

example (a : Rat) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by
  linarith

example (x y : Rat) (h : x < y) : x ≠ y := by linarith

example (x y : Rat) (h : x < y) : ¬ x = y := by linarith

-- Check `linarith!` works as expected
example (x : Rat) : id x ≥ x := by
  fail_if_success
    linarith
  linarith!

opaque Nat.prime : ℕ → Prop

example (x y z : Rat) (h1 : 2 * x + ((-3) * y) < 0) (h2 : (-4) * x + 2 * z < 0) (h3 : 12 * y + (-4) * z < 0)
    (h4 : Nat.prime 7) : False := by
  linarith

example (x y z : Rat) (h1 : 2 * 1 * x + (3) * (y * (-1)) < 0) (h2 : (-2) * x * 2 < -(z + z))
    (h3 : 12 * y + (-4) * z < 0) (h4 : Nat.prime 7) : False := by
  linarith

example (w x y z : ℤ) (h1 : 4 * x + (-3) * y + 6 * w ≤ 0) (h2 : (-1) * x < 0) (h3 : y < 0) (h4 : w ≥ 0)
    (h5 : Nat.prime x.natAbs) : False := by
  linarith

section term_arguments

example (x : Rat) (hx : x > 0) (h : x.num < 0) : False := by
  linarith [Rat.num_pos.mpr hx, h]

example (x : Rat) (hx : x > 0) (h : x.num < 0) : False := by
  fail_if_success
    linarith
  fail_if_success
    linarith only [h]
  fail_if_success
    linarith only [Rat.num_pos.mpr hx]
  linarith only [Rat.num_pos.mpr hx, h]

end term_arguments

example (i n : ℕ) (h : (2 : ℤ) ^ i ≤ 2 ^ n) : (0 : ℤ) ≤ 2 ^ n - 2 ^ i := by
  linarith

-- Check we use `exfalso` on non-comparison goals.
example (a b c : Rat) (h2 : b > 0) (h3 : b < 0) : Nat.prime 10 := by
  linarith

example (a b c : Rat) (h2 : (2 : Rat) > 3) : a + b - c ≥ 3 := by
  linarith -exfalso

-- Verify that we split conjunctions in hypotheses.
example (x y : Rat)
    (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3 ∧ (x + 4) * x ≥ 0 ∧ (6 + 3 * y) * y ≥ 0) :
    False := by
  fail_if_success linarith -splitHypotheses
  linarith

example (h : 1 < 0) (g : ¬ 37 < 42) (k : True) (l : (-7 : ℤ) < 5) : 3 < 7 := by
  linarith [(rfl : 0 = 0)]

example (h : 1 < 0) : 3 = 7 := by
  linarith [Int.zero_lt_one]

example (h1 : (1 : ℕ) < 1) : False := by
  linarith

example (a b c : ℕ) : a + b ≥ a := by
  linarith

example (a b i : ℕ) (h1 : ¬ a < i) (h2 : b < i) (h3 : a ≤ b) : False := by
  linarith

example (x y : ℕ) (h : x < 3 * y) : True := by
  zify at h
  trivial

example : (Nat.cast 2 : ℤ) = 2 := Nat.cast_ofNat

example (x y z : ℕ) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  linarith

example (a b c : ℕ) : ¬ a + b < a := by
  linarith

example (n : ℕ) (h1 : n ≤ 3) (h2 : n > 2) : n = 3 := by
  linarith

example (z : ℕ) (hz : ¬ z ≥ 2) (h2 : ¬ z + 1 ≤ 2) : False := by
  linarith

example (z : ℕ) (hz : ¬ z ≥ 2) : z + 1 ≤ 2 := by
  linarith

example (i : ℤ) (hi : i > 5) : 2 * i + 3 > 11 := by
  linarith

example (m : ℕ) : m * m + m + (2 * m + 2) = m * m + m + (m + 1) + (m + 1) := by
  linarith

example (mess : ℕ → ℕ) (S n : ℕ) :
    mess S + (n * mess S + n * 2 + 1) < n * mess S + mess S + (n * 2 + 2) := by
  linarith

example (p n p' n' : ℕ) (h : p + n' = p' + n) : n + p' = n' + p := by
  linarith

example (a b c : ℚ) (h1 : 1 / a < b) (h2 : b < c) : 1 / a < c := by
  linarith

example (N : ℕ) (n : ℕ) (Hirrelevant : n > N) (A : Rat) (l : Rat) (h : A - l ≤ -(A - l))
    (h_1 : ¬A ≤ -A) (h_2 : ¬l ≤ -l) (h_3 : -(A - l) < 1) : A < l + 1 := by
  linarith

example (d : Rat) (q n : ℕ) (h1 : ((q : Rat) - 1) * n ≥ 0) (h2 : d = 2 / 3 * (((q : Rat) - 1) * n)) :
    d ≤ ((q : Rat) - 1) * n := by
  linarith

example (d : Rat) (q n : ℕ) (h1 : ((q : Rat) - 1) * n ≥ 0) (h2 : d = 2 / 3 * (((q : Rat) - 1) * n)) :
    ((q : Rat) - 1)*n - d = 1/3 * (((q : Rat) - 1) * n) := by
  linarith

example (x y z : ℚ) (hx : x < 5) (hx2 : x > 5) (hy : y < 5000000000) (hz : z > 34 * y) : false := by
  linarith only [hx, hx2]

example (x y z : ℚ) (hx : x < 5) (hy : y < 5000000000) (hz : z > 34 * y) : x ≤ 5 := by
  linarith only [hx]

/- The speed of `linarith` is very sensitive to how much typeclass inference is demanded by the
lemmas it orchestrates.

This example took 3318 heartbeats (and 110 ms on a good laptop) on an earlier implementation, which
in several places used off-the-shelf library lemmas requiring low-level typeclasses, e.g.
`Add{Left,Right}{Strict}Mono`.

After a tweak to rely only on custom `linarith` clones of these lemmas taking high-level typeclasses,
this now (November 2024) takes 1647 heartbeats (63 ms on a good laptop). -/
set_option maxHeartbeats 2000 in
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x y : K}
    (h : x + y = 10) (h' : x + 2 * y ≤ 18) (h : x < 2) : False := by
  linarith (config := {discharger := testSorryTac})

example (u v x y A B : ℚ)
    (a : 0 < A)
    (a_1 : 0 <= 1 - A)
    (a_2 : 0 <= B - 1)
    (a_3 : 0 <= B - x)
    (a_4 : 0 <= B - y)
    (a_5 : 0 <= u)
    (a_6 : 0 <= v)
    (a_7 : 0 < A - u)
    (a_8 : 0 < A - v) :
    u * y + v * x + u * v < 3 * A * B := by
  nlinarith

example (u v x y A B : ℚ) : (0 < A) → (A ≤ 1) → (1 ≤ B)
    → (x ≤ B) → (y ≤ B)
    → (0 ≤ u ) → (0 ≤ v )
    → (u < A) → (v < A)
    → (u * y + v * x + u * v < 3 * A * B) := by
  intros
  nlinarith

example (u v x y A B : Rat)
    (a_7 : 0 < A - u)
    (a_8 : 0 < A - v) :
    (0 <= A * (1 - A))
    -> (0 <= A * (B - 1))
    -> (0 < A * (A - u))
    -> (0 <= (B - 1) * (A - u))
    -> (0 <= (B - 1) * (A - v))
    -> (0 <= (B - x) * v)
    -> (0 <= (B - y) * u)
    -> (0 <= u * (A - v))
    -> u * y + v * x + u * v < 3 * A * B := by
  intros
  linarith

example (u v x y A B : Rat)
    (a : 0 < A)
    (a_1 : 0 <= 1 - A)
    (a_2 : 0 <= B - 1)
    (a_3 : 0 <= B - x)
    (a_4 : 0 <= B - y)
    (a_5 : 0 <= u)
    (a_6 : 0 <= v)
    (a_7 : 0 < A - u)
    (a_8 : 0 < A - v) :
    (0 < A * A)
    -> (0 <= A * (1 - A))
    -> (0 <= A * (B - 1))
    -> (0 <= A * (B - x))
    -> (0 <= A * (B - y))
    -> (0 <= A * u)
    -> (0 <= A * v)
    -> (0 < A * (A - u))
    -> (0 < A * (A - v))
    -> (0 <= (1 - A) * A)
    -> (0 <= (1 - A) * (1 - A))
    -> (0 <= (1 - A) * (B - 1))
    -> (0 <= (1 - A) * (B - x))
    -> (0 <= (1 - A) * (B - y))
    -> (0 <= (1 - A) * u)
    -> (0 <= (1 - A) * v)
    -> (0 <= (1 - A) * (A - u))
    -> (0 <= (1 - A) * (A - v))
    -> (0 <= (B - 1) * A)
    -> (0 <= (B - 1) * (1 - A))
    -> (0 <= (B - 1) * (B - 1))
    -> (0 <= (B - 1) * (B - x))
    -> (0 <= (B - 1) * (B - y))
    -> (0 <= (B - 1) * u)
    -> (0 <= (B - 1) * v)
    -> (0 <= (B - 1) * (A - u))
    -> (0 <= (B - 1) * (A - v))
    -> (0 <= (B - x) * A)
    -> (0 <= (B - x) * (1 - A))
    -> (0 <= (B - x) * (B - 1))
    -> (0 <= (B - x) * (B - x))
    -> (0 <= (B - x) * (B - y))
    -> (0 <= (B - x) * u)
    -> (0 <= (B - x) * v)
    -> (0 <= (B - x) * (A - u))
    -> (0 <= (B - x) * (A - v))
    -> (0 <= (B - y) * A)
    -> (0 <= (B - y) * (1 - A))
    -> (0 <= (B - y) * (B - 1))
    -> (0 <= (B - y) * (B - x))
    -> (0 <= (B - y) * (B - y))
    -> (0 <= (B - y) * u)
    -> (0 <= (B - y) * v)
    -> (0 <= (B - y) * (A - u))
    -> (0 <= (B - y) * (A - v))
    -> (0 <= u * A)
    -> (0 <= u * (1 - A))
    -> (0 <= u * (B - 1))
    -> (0 <= u * (B - x))
    -> (0 <= u * (B - y))
    -> (0 <= u * u)
    -> (0 <= u * v)
    -> (0 <= u * (A - u))
    -> (0 <= u * (A - v))
    -> (0 <= v * A)
    -> (0 <= v * (1 - A))
    -> (0 <= v * (B - 1))
    -> (0 <= v * (B - x))
    -> (0 <= v * (B - y))
    -> (0 <= v * u)
    -> (0 <= v * v)
    -> (0 <= v * (A - u))
    -> (0 <= v * (A - v))
    -> (0 < (A - u) * A)
    -> (0 <= (A - u) * (1 - A))
    -> (0 <= (A - u) * (B - 1))
    -> (0 <= (A - u) * (B - x))
    -> (0 <= (A - u) * (B - y))
    -> (0 <= (A - u) * u)
    -> (0 <= (A - u) * v)
    -> (0 < (A - u) * (A - u))
    -> (0 < (A - u) * (A - v))
    -> (0 < (A - v) * A)
    -> (0 <= (A - v) * (1 - A))
    -> (0 <= (A - v) * (B - 1))
    -> (0 <= (A - v) * (B - x))
    -> (0 <= (A - v) * (B - y))
    -> (0 <= (A - v) * u)
    -> (0 <= (A - v) * v)
    -> (0 < (A - v) * (A - u))
    -> (0 < (A - v) * (A - v))
    -> u * y + v * x + u * v < 3 * A * B := by
  intros
  linarith

example (A B : ℚ) : (0 < A) → (1 ≤ B) → (0 < A / 8 * B) := by
  intros
  nlinarith

example (x y : ℚ) : 0 ≤ x ^2 + y ^2 := by
  nlinarith

example (x y : ℚ) : 0 ≤ x*x + y*y := by
  nlinarith

example (x y : ℚ) : x = 0 → y = 0 → x*x + y*y = 0 := by
  intros
  nlinarith

lemma norm_eq_zero_iff {x y : ℚ} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro
    constructor <;>
      nlinarith
  · intro; nlinarith

lemma norm_zero_left {x y : ℚ} (h1 : x * x + y * y = 0) : x = 0 := by
  nlinarith

lemma norm_nonpos_right {x y : ℚ} (h1 : x * x + y * y ≤ 0) : y = 0 := by
  nlinarith

lemma norm_nonpos_left (x y : ℚ) (h1 : x * x + y * y ≤ 0) : x = 0 := by
  nlinarith

section
variable {E : Type _} [AddGroup E]
example (f : ℤ → E) (h : 0 = f 0) : 1 ≤ 2 := by nlinarith
example (a : E) (h : a = a) : 1 ≤ 2 := by nlinarith
end

-- Note: This takes a huge amount of time with the Fourier-Motzkin oracle
example (a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 d3 : ℕ)
    (h1 : a1 + a2 + a3 = b1 + b2 + b3)
    (h2 : c1 + c2 + c3 = d1 + d2 + d3) :
    a1 * c1 + a2 * c1 + a3 * c1 + a1 * c2 + a2 * c2 + a3 * c2 + a1 * c3 + a2 * c3 + a3 * c3 =
    b1 * d1 + b2 * d1 + b3 * d1 + b1 * d2 + b2 * d2 + b3 * d2 + b1 * d3 + b2 * d3 + b3 * d3 := by
  nlinarith --(oracle := some .fourierMotzkin)

-- This should not be slower than the example below with the Fourier-Motzkin oracle
example (p q r s t u v w : ℕ) (h1 : p + u = q + t) (h2 : r + w = s + v) :
    p * r + q * s + (t * w + u * v) = p * s + q * r + (t * v + u * w) := by
  nlinarith

example (p q r s t u v w : ℕ) (h1 : p + u = q + t) (h2 : r + w = s + v) :
    p * r + q * s + (t * w + u * v) = p * s + q * r + (t * v + u * w) := by
  nlinarith (oracle := .fourierMotzkin)

section
-- Tests involving a norm, including that squares in a type where `sq_nonneg` does not apply
-- do not cause an exception
variable {R : Type _} [Ring R] (abs : R → ℚ)

axiom abs_nonneg' : ∀ r, 0 ≤ abs r

example (t : R) (a b : ℚ) (h : a ≤ b) : abs (t^2) * a ≤ abs (t^2) * b := by
  nlinarith [abs_nonneg' abs (t^2)]

example (t : R) (a b : ℚ) (h : a ≤ b) : a ≤ abs (t^2) + b := by
  linarith [abs_nonneg' abs (t^2)]

example (t : R) (a b : ℚ) (h : a ≤ b) : abs t * a ≤ abs t * b := by
  nlinarith [abs_nonneg' abs t]

end

axiom T : Type

@[instance] axiom T.ring : Ring T
@[instance] axiom T.partialOrder : PartialOrder T
@[instance] axiom T.isOrderedRing : IsOrderedRing T

namespace T

axiom zero_lt_one : (0 : T) < 1

lemma works {a b : ℕ} (hab : a ≤ b) (h : b < a) : false := by
  linarith

end T

example (a b c : ℚ) (h : a ≠ b) (h3 : b ≠ c) (h2 : a ≥ b) : b ≠ c := by
  linarith +splitNe

example (a b c : ℚ) (h : a ≠ b) (h2 : a ≥ b) (h3 : b ≠ c) : a > b := by
  linarith +splitNe

example (a b : ℕ) (h1 : b ≠ a) (h2 : b ≤ a) : b < a := by
  linarith +splitNe

example (a b : ℕ) (h1 : b ≠ a) (h2 : ¬a < b) : b < a := by
  linarith +splitNe

section
-- Regression test for issue that splitNe didn't see `¬ a = b`

example (a b : Nat) (h1 : a < b + 1) (h2 : a ≠ b) : a < b := by
  linarith +splitNe

example (a b : Nat) (h1 : a < b + 1) (h2 : ¬ a = b) : a < b := by
  linarith +splitNe

end

-- Checks that splitNe handles metavariables and also that conjunction splitting occurs
-- before splitNe splitting
example (r : ℚ) (h' : 1 = r * 2) : 1 = 0 ∨ r = 1 / 2 := by
  by_contra! h''
  linarith +splitNe

example (x y : ℚ) (h₁ : 0 ≤ y) (h₂ : y ≤ x) : y * x ≤ x * x := by nlinarith

example (x y : ℚ) (h₁ : 0 ≤ y) (h₂ : y ≤ x) : y * x ≤ x ^ 2 := by nlinarith

axiom foo {x : Int} : 1 ≤ x → 1 ≤ x*x
lemma bar (x y : Int) (h : 0 ≤ y ∧ 1 ≤ x) : 1 ≤ y + x * x := by linarith [foo h.2]

-- -- issue https://github.com/leanprover-community/mathlib4/pull/9822
-- lemma mytest (j : ℕ) (h : 0 < j) : j-1 < j := by linarith

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (h : ∃ x : α, 0 ≤ x) : True := by
  obtain ⟨x, h⟩ := h
  have : 0 ≤ x := by linarith
  trivial

-- At one point, this failed, due to `mdata` interfering with `Expr.isEq`.
example (a : Int) : a = a := by
  have h : True := True.intro
  linarith

example (n : Nat) (h1 : ¬n = 1) (h2 : n ≥ 1) : n ≥ 2 := by
  by_contra h3
  suffices n = 1 by exact h1 this
  linarith

example (n : Nat) (h1 : ¬n = 1) (h2 : n ≥ 1) : n ≥ 2 := by
  have h4 : n ≥ 1 := h2
  by_contra h3
  suffices n = 1 by exact h1 this
  linarith

universe u v
-- simulate the type of MvPolynomial
def P : Type u → Type v → Sort (max (u+1) (v+1)) := test_sorry
noncomputable instance {c d} : Field (P c d) := test_sorry
noncomputable instance {c d} : LinearOrder (P c d) := test_sorry
noncomputable instance {c d} : IsStrictOrderedRing (P c d) := test_sorry

example (p : P PUnit.{u + 1} PUnit.{v + 1}) (h : 0 < p) : 0 < 2 * p := by
  linarith

example (n : Nat) : n + 1 ≥ (1 / 2 : ℚ) := by linarith

example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (n : Nat) : (5 : α) - (n : α) ≤ (6 : α) := by
  linarith

example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (n : Nat) : -(n : α) ≤ 0 := by
  linarith

example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : Nat) (a : α) (h : a ≥ 2) : a * (n : α) + 5 ≥ 4 := by nlinarith
example (x : ℚ) (h : x * (2⁻¹ + 2 / 3) = 1) : x = 6 / 7 := by linarith

example {α} [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] (x : α) (_ : 0 ≤ x) :
    0 ≤ 1 := by linarith

example (k : ℤ) (h : k < 1) (h₁ : -1 < k) : k = 0 := by
  -- Make h₁'s type be a metavariable. At one point this caused the strengthenStrictInt
  -- linarith preprocessor to fail.
  change _ at h₁
  linarith

/-- error: unknown identifier 'garbage' -/
#guard_msgs in
example (q : Prop) (p : ∀ (x : ℤ), q → 1 = 2) : 1 = 2 := by
  linarith [p _ garbage]

/-- error: unknown identifier 'garbage' -/
#guard_msgs in
example (q : Prop) (p : ∀ (x : ℤ), q → 1 = 2) : 1 = 2 := by
  nlinarith [p _ garbage]

/--
error: don't know how to synthesize placeholder for argument 'x'
context:
q : Prop
p : ∀ (x : ℤ), 1 = 2
⊢ ℤ
---
error: unsolved goals
q : Prop
p : ∀ (x : ℤ), 1 = 2
⊢ 1 = 2
-/
#guard_msgs in
example (q : Prop) (p : ∀ (x : ℤ), 1 = 2) : 1 = 2 := by
  linarith [p _]

/--
error: Argument passed to linarith has metavariables:
  p ?a
-/
#guard_msgs in
example (q : Prop) (p : ∀ (x : ℤ), 1 = 2) : 1 = 2 := by
  linarith [p ?a]

/--
error: Argument passed to nlinarith has metavariables:
  p ?a
-/
#guard_msgs in
example (q : Prop) (p : ∀ (x : ℤ), 1 = 2) : 1 = 2 := by
  nlinarith [p ?a]

example (h : False): True := by
  have : ∑ k ∈ Finset.empty, k^2 = 0 := by contradiction
  have : ∀ k : Nat, 0 ≤ k := by
    intro h
    -- this should not panic:
    nlinarith
  trivial

example (x : Nat) : 0 ≤ x ^ 9890 := by
  fail_if_success linarith -- this should not stack overflow
  apply zero_le

/-- https://github.com/leanprover-community/mathlib4/issues/8875 -/
example (a b c d e : ℚ)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) :
    e = 3 := by
  linarith

/-- https://github.com/leanprover-community/mathlib4/issues/2717 -/
example {x1 x2 x3 x4 x5 x6 x7 x8 : ℚ} :
    (3 * x4 - x3 - x2 - x1 : ℚ) < 0 →
    x5 - x4 < 0 →
    2 * (x5 - x4) < 0 →
    -x6 + x3 < 0 →
    -x6 + x2 < 0 →
    2 * (x6 - x5) < 0 →
    x8 - x7 < 0 →
    -x8 + x2 < 0 →
    -x8 + x7 - x5 + x1 < 0 →
    x7 - x5 < 0 →
    False := by
  intros; linarith

#guard_msgs in
/-- https://github.com/leanprover-community/mathlib4/issues/8875 -/
example (a b c d e : ℚ)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) :
    e = 3 := by
  linarith (oracle := .fourierMotzkin)

#guard_msgs in
/-- https://github.com/leanprover-community/mathlib4/issues/2717 -/
example {x1 x2 x3 x4 x5 x6 x7 x8 : ℚ} :
    (3 * x4 - x3 - x2 - x1 : ℚ) < 0 →
    x5 - x4 < 0 →
    2 * (x5 - x4) < 0 →
    -x6 + x3 < 0 →
    -x6 + x2 < 0 →
    2 * (x6 - x5) < 0 →
    x8 - x7 < 0 →
    -x8 + x2 < 0 →
    -x8 + x7 - x5 + x1 < 0 →
    x7 - x5 < 0 → False := by
  intros
  linarith (oracle := .fourierMotzkin)

section findSquares

private abbrev wrapped (z : ℤ) : ℤ := z
/-- the `findSquares` preprocessor can look through reducible defeq -/
example (x : ℤ) : 0 ≤ x * wrapped x := by nlinarith

private def tightlyWrapped (z : ℤ) : ℤ := z
/--
error: linarith failed to find a contradiction
case h
x : ℤ
a✝ : x * tightlyWrapped x < 0
⊢ False
failed
-/
#guard_msgs in
example (x : ℤ) : 0 ≤ x * tightlyWrapped x := by nlinarith

end findSquares

-- `Expr.mdata` should be ignored by linarith
example (x : Int) (h : x = -2) : x = no_index(-2) := by
  linarith [h]
