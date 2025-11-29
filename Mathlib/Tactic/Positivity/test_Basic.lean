import Mathlib.Tactic.Positivity.Basic

/-! # Tests for the `positivity` tactic

This tactic proves goals of the form `0 ≤ a` and `0 < a`.
-/
set_option autoImplicit true
set_option trace.Tactic.positivity true
set_option trace.Tactic.positivity.failure true

open Function Nat

variable {ι α β E : Type*}

/- ## Numeric goals -/

example : 0 ≤ 0 := by positivity

example : 0 ≤ 3 := by positivity

example : 0 < 3 := by positivity
-- example : (0 : EReal) < 2 := by positivity
-- example : 0 < (2 : EReal) := by positivity
-- example : (0 : EReal) < 2 := by positivity

-- example : (0 : ℝ≥0∞) ≤ 1 := by positivity
-- example : (0 : ℝ≥0∞) ≤ 0 := by positivity
-- example : (0 : EReal) ≤ 0 := by positivity
-- example : 0 ≤ (2 : EReal) := by positivity

/- ## Goals working directly from a hypothesis -/

section FromHypothesis

-- set_option trace.Meta.debug true
-- sudo set_option trace.Tactic.positivity true
example {a : ℤ} (ha : 0 < a) : 0 < a := by positivity
example {a : ℤ} (ha : 0 < a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 0 < a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 0 ≤ a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : a ≠ 0) : a ≠ 0 := by positivity
example {a : ℤ} (ha : a = 0) : 0 ≤ a := by positivity

section

variable [Zero α] [PartialOrder α] {a : α}

example (ha : 0 < a) : 0 < a := by positivity
example (ha : 0 < a) : 0 ≤ a := by positivity
example (ha : 0 < a) : a ≠ 0 := by positivity
example (ha : 0 ≤ a) : 0 ≤ a := by positivity
example (ha : a ≠ 0) : a ≠ 0 := by positivity
example (ha : a = 0) : 0 ≤ a := by positivity

end

/- ### Reversing hypotheses -/

example {a : ℤ} (ha : a > 0) : 0 < a := by positivity
example {a : ℤ} (ha : a > 0) : 0 ≤ a := by positivity
example {a : ℤ} (ha : a > 0) : a ≥ 0 := by positivity
example {a : ℤ} (ha : a > 0) : a ≠ 0 := by positivity
example {a : ℤ} (ha : a ≥ 0) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 0 ≠ a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 0 < a) : a > 0 := by positivity
example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by positivity
example {a : ℤ} (ha : 0 < a) : 0 ≠ a := by positivity
example {a : ℤ} (ha : 0 ≤ a) : a ≥ 0 := by positivity
example {a : ℤ} (ha : a ≠ 0) : 0 ≠ a := by positivity
example {a : ℤ} (ha : a = 0) : a ≥ 0 := by positivity
example {a : ℤ} (ha : 0 = a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 0 = a) : a ≥ 0 := by positivity

end FromHypothesis

/- ### Calling `norm_num` -/

example {a : ℤ} (ha : 3 = a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 3 = a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 3 = a) : 0 < a := by positivity
example {a : ℤ} (ha : a = -1) : a ≠ 0 := by positivity

example {a : ℤ} (ha : 3 ≤ a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 3 ≤ a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 3 ≤ a) : 0 < a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a := by positivity
example {a : ℤ} (ha : 3 < a) : a ≠ 0 := by positivity
example {a : ℤ} (ha : 3 < a) : 0 < a := by positivity

example {a b : ℤ} (h : 0 ≤ a + b) : 0 ≤ a + b := by positivity

example {a : ℤ} (hlt : 0 ≤ a) (hne : a ≠ 0) : 0 < a := by positivity

example {a b c d : ℤ} (ha : c < a) (hb : d < b) : 0 < (a - c) * (b - d) := by
  positivity [sub_pos_of_lt ha, sub_pos_of_lt hb]

section

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

example : (1/4 - 2/3 : ℚ) ≠ 0 := by positivity
example : (1/4 - 2/3 : α) ≠ 0 := by positivity

end

/- ### `ArithmeticFunction.sigma` and `ArithmeticFunction.zeta` -/

-- example (a b : ℕ) (hb : 0 < b) : 0 < ArithmeticFunction.sigma a b := by positivity
-- example (a : ℕ) (ha : 0 < a) : 0 < ArithmeticFunction.zeta a := by positivity

/-
## Test for meta-variable instantiation

Reported on
https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/New.20tactic.3A.20.60positivity.60/near/300639970
-/

example : 0 ≤ 0 := by apply le_trans _ (le_refl _); positivity


/- ## Tests of the @[positivity] plugin tactics (addition, multiplication, division) -/

-- example [Nonempty ι] [Zero α] {a : α} (ha : a ≠ 0) : const ι a ≠ 0 := by positivity
-- example [Zero α] [PartialOrder α] {a : α} (ha : 0 < a) : 0 ≤ const ι a := by positivity
-- example [Zero α] [PartialOrder α] {a : α} (ha : 0 ≤ a) : 0 ≤ const ι a := by positivity
-- example [Nonempty ι] [Zero α] [PartialOrder α] {a : α} (ha : 0 < a) : 0 < const ι a := by
--  positivity

section ite
variable {p : Prop} [Decidable p] {a b : ℤ}

example (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by positivity
example (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by positivity
example (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ ite p a b := by positivity
example (ha : 0 < a) (hb : b ≠ 0) : ite p a b ≠ 0 := by positivity
example (ha : a ≠ 0) (hb : 0 < b) : ite p a b ≠ 0 := by positivity
example (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by positivity

end ite

section MinMax

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < min a b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ min a b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ min a b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ min a b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : min a b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : min a b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : min a b ≠ 0 := by positivity

example {a b : ℚ} (ha : 0 < a) : 0 < max a b := by positivity
example {a b : ℚ} (hb : 0 < b) : 0 < max a b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) : 0 ≤ max a b := by positivity
example {a b : ℚ} (hb : 0 ≤ b) : 0 ≤ max a b := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : max a b ≠ 0 := by positivity

example : 0 ≤ max 3 4 := by positivity
example : 0 ≤ max (0 : ℤ) (-3) := by positivity
example : 0 ≤ max (-3 : ℤ) 5 := by positivity

end MinMax

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a * b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a * b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by positivity

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by positivity
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 := by positivity
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by positivity

example {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b := by positivity
example {a : ℤ} (ha : 0 < a) : 0 < a / a := by positivity
example {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity
example {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by positivity
example {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by positivity

example {a : ℚ} (ha : 0 < a) : 0 < a⁻¹ := by positivity
example {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by positivity
example {a : ℚ} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by positivity

example {a : ℚ} (n : ℕ) (ha : 0 < a) : 0 < a ^ n := by positivity
example {a : ℚ} (n : ℕ) (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example {a : ℚ} (n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by positivity
example {a : ℚ} : 0 ≤ a ^ 18 := by positivity
example {a : ℚ} (ha : a ≠ 0) : 0 < a ^ 18 := by positivity

example {a : ℚ} (ha : 0 < a) : 0 < |a| := by positivity
example {a : ℚ} (ha : a ≠ 0) : 0 < |a| := by positivity
example (a : ℚ) : 0 ≤ |a| := by positivity

example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by positivity
example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b := by positivity
example {a : ℤ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b := by positivity
example {a : ℤ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a • b := by positivity
example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 := by positivity
example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 := by positivity
example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a • b ≠ 0 := by positivity

-- Test that the positivity extension for `a • b` can handle universe polymorphism.
-- example {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
--     [Semiring M] [PartialOrder M] [IsStrictOrderedRing M]
--     [SMulWithZero R M] [PosSMulStrictMono R M] {a : R} {b : M} (ha : 0 < a) (hb : 0 < b) :
--     0 < a • b := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 ≤ 3 + a + b + b + 14 := by positivity

example {H : Type*} [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
    {a b : H} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ a + a + b := by
  positivity

example {a : ℤ} (ha : 3 < a) : 0 < a + a := by positivity

example {a b : ℚ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

section
variable {q : ℚ}

example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.den := by positivity
example (hq : 0 < q) : 0 < q := by positivity
example (hq : 0 ≤ q) : 0 ≤ q.num := by positivity

end

example (a b : ℕ) (ha : a ≠ 0) : 0 < a.gcd b := by positivity
example (a b : ℤ) (ha : a ≠ 0) : 0 < a.gcd b := by positivity
example (a b : ℕ) (hb : b ≠ 0) : 0 < a.gcd b := by positivity
example (a b : ℤ) (hb : b ≠ 0) : 0 < a.gcd b := by positivity
example (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a.lcm b := by positivity
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a.lcm b := by positivity
example (a : ℕ) (ha : a ≠ 0) : 0 < a.sqrt := by positivity
-- example (a : ℕ) (ha : a ≠ 0) : 0 < a.totient := by positivity
