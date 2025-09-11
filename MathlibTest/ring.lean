import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true

-- We deliberately mock R here so that we don't have to import the deps
axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.field : Field ℝ
@[instance] axiom Real.linearOrder : LinearOrder ℝ
@[instance] axiom Real.isStrictOrderedRing : IsStrictOrderedRing ℝ

example {a b c : ℝ} {f : ℝ → ℝ} (h : f (a * c * b) * f (c + b + a) = 1) :
    f (a + b + c) * f (b * a * c) = 1 := by
  ring_nf at *
  exact h

example (x y : ℕ) : x + y = y + x := by ring
example (x y : ℕ) : x + y + y = 2 * y + x := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x y : ℕ+) : x + y = y + x := by ring
example {α} [CommRing α] (x y : α) : x + y + y - x = 2 * y := by ring
example {α} [CommSemiring α] (x y : α) : (x + y)^2 = x^2 + 2 • x * y + y^2 := by ring

example (x y : ℕ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example (x y : ℕ+) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example {α} [CommSemiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by ring
example (n : ℕ) : (n / 2) + (n / 2) = 2 * (n / 2) := by ring
example {α} [Field α] [CharZero α] (a : α) : a / 2 = a / 2 := by ring
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) :
  a * (-c / b) * (-c / b) + -c + c = a * (c / b * (c / b)) := by ring
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example {α} [CommSemiring α] (x : α) : x ^ (2 + 2) = x^4 := by ring1
example {α} [CommSemiring α] (x : α) : x ^ (2 + 2) = x^4 := by ring
example {α} [CommRing α] (x : α) : x ^ 2 = x * x := by ring
-- example {α} [CommRing α] (x : α) : x ^ (2 : ℤ) = x * x := by ring
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) :
  b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring
example {α} [CommSemiring α] (x y z : α) (n : ℕ) :
  (x + y) * (z * (y * y) + (x * x ^ n + (1 + ↑n) * x ^ n * y)) =
  x * (x * x ^ n) + ((2 + ↑n) * (x * x ^ n) * y +
    (x * z + (z * y + (1 + ↑n) * x ^ n)) * (y * y)) := by ring
example {α} [CommRing α] (a b c d e : α) :
  (-(a * b) + c + d) * e = (c + (d + -a * b)) * e := by ring
example (a n s : ℕ) : a * (n - s) = (n - s) * a := by ring

section Rat

variable [Field α]

example (x : ℚ) : x / 2 + x / 2 = x := by ring
example (x : α) : x / 2 = x / 2 := by ring1
example : (1 + 1)⁻¹ = (2⁻¹ : α) := by ring1
example (x : α) : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by ring1
example (x : α) : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by ring1
example (x y : α) : x * y⁻¹ = y⁻¹ * x := by ring1

example (x y : α) : (x^2 * y)⁻¹ = (y * x^2)⁻¹ := by ring1
example (x y : α) : (x^2)⁻¹ / y = (y * x^2)⁻¹ := by ring1
example (x y : α) : 3 / (x - x + y)⁻¹ = 3 * (x + y⁻¹ - x)⁻¹ := by ring1

variable [CharZero α]

example (x : α) : x / 2 = x / 2 := by ring
example (x : α) : (x : α) = x * (5/3)*(3/5) := by ring1

end Rat

example (A : ℕ) : (2 * A) ^ 2 = (2 * A) ^ 2 := by ring

example (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x / (y / z) + y ⁻¹ + 1 / (y * -x) = -1/ (x * y) + (x * z + 1) / y := by
  field_simp
  ring

example (a b c d x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x - c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x - c) / x) := by
  field_simp
  ring

example : (876544 : ℤ) * -1 + (1000000 - 123456) = 0 := by ring

example (x : ℝ) (hx : x ≠ 0) :
    2 * x ^ 3 * 2 / (24 * x) = x ^ 2 / 6 := by
  field_simp
  ring

-- As reported at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/ring_nf.20failing.20to.20fully.20normalize
example (x : ℤ) (h : x - x + x = 0) : x = 0 := by
  ring_nf at h
  exact h

-- this proof style is not recommended practice
example (A B : ℕ) (H : B * A = 2) : A * B = 2 := by ring_nf at H ⊢; exact H

example (f : ℕ → ℕ) :
  2 + f (2 * f 3 * f 3) + f 3 = 1 + f (f 3 ^ 2 + f 3 * f 3) + 1 + f (2 + 1) := by ring_nf

example (n : ℕ) (m : ℤ) : 2^(n + 1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!

-- Example with ring discharging the goal
example : 22 + 7 * 4 + 3 * 8 = 0 + 7 * 4 + 46 := by
  conv => ring
  trivial -- FIXME: not needed in lean 3

-- Example with ring failing to discharge, to normalizing the goal

/-- info: Try this: ring_nf -/
#guard_msgs in
example : (22 + 7 * 4 + 3 * 8 = 0 + 7 * 4 + 47) = (74 = 75) := by
  conv => ring
  trivial

-- Example with ring discharging the goal
example (x : ℕ) : 22 + 7 * x + 3 * 8 = 0 + 7 * x + 46 := by
  conv => ring
  trivial

-- Example with ring failing to discharge, to normalizing the goal

/-- info: Try this: ring_nf -/
#guard_msgs in
example (x : ℕ) : (22 + 7 * x + 3 * 8 = 0 + 7 * x + 46 + 1)
                    = (7 * x + 46 = 7 * x + 47) := by
  conv => ring
  trivial

-- check that mdata is consumed
noncomputable def f : Nat → Nat := test_sorry

example (a : Nat) : 1 * f a * 1 = f (a + 0) := by
  have ha : a + 0 = a := by ring
  rw [ha] -- goal has mdata
  ring1

-- check that mdata is consumed by ring_nf
example (a b : ℤ) : a+b=0 ↔ b+a=0 := by
  have : 3 = 3 := rfl
  ring_nf -- reduced to `True` with mdata

-- Powers in the exponent get evaluated correctly
example (X : ℤ) : (X^5 + 1) * (X^2^3 + X) = X^13 + X^8 + X^6 + X := by ring

-- simulate the type of MvPolynomial
def R : Type u → Type v → Sort (max (u+1) (v+1)) := test_sorry
noncomputable instance : CommRing (R a b) := test_sorry

example (p : R PUnit.{u + 1} PUnit.{v + 1}) : p + 0 = p := by
  ring
example (p q : R PUnit.{u + 1} PUnit.{v + 1}) : p + q = q + p := by
  ring


example (p : R PUnit.{u + 1} PUnit.{v + 1}) : p + 0 = p := by
  ring_nf
example (p q : R PUnit.{u + 1} PUnit.{v + 1}) : p + q = q + p := by
  ring_nf

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/ring_nf.20returns.20ugly.20literals/near/400988184
example {n : ℝ} :
    (n + 1 / 2) ^ 2 * (n + 1 + 1 / 3) = 1 / 3 + n * (19 / 12) + n ^ 2 * (7 / 3) + n ^ 3 := by
  -- `conv_lhs` prevents `ring_nf` picking a bad normalization for both sides.
  conv_lhs => ring_nf

-- We can't use `guard_target =ₛ` here, as while it does detect stray `OfNat`s, it also complains
-- about differing instance paths.
/--
trace: n : ℝ
_hn : 0 ≤ n
⊢ 1 / 3 + n * (19 / 12) + n ^ 2 * (7 / 3) + n ^ 3 ≤ 1 / 3 + n * (5 / 3) + n ^ 2 * (7 / 3) + n ^ 3
-/
#guard_msgs (trace) in
example {n : ℝ} (_hn : 0 ≤ n) : (n + 1 / 2) ^ 2 * (n + 1 + 1 / 3) ≤ (n + 1 / 3) * (n + 1) ^ 2 := by
  ring_nf
  trace_state
  exact test_sorry

section
abbrev myId (a : ℤ) : ℤ := a

/-
Test that when `ring_nf` normalizes multiple expressions which contain a particular atom, it uses a
form for that atom which is consistent between expressions.

We can't use `guard_hyp h :ₛ` here, as while it does tell apart `x` and `myId x`, it also complains
about differing instance paths.
-/
/--
trace: x : ℤ
R : ℤ → ℤ → Prop
h : R (myId x * 2) (myId x * 2)
⊢ True
-/
#guard_msgs (trace) in
example (x : ℤ) (R : ℤ → ℤ → Prop) : True := by
  have h : R (myId x + x) (x + myId x) := test_sorry
  ring_nf at h
  trace_state
  trivial

end

-- new behaviour as of https://github.com/leanprover-community/mathlib4/issues/27562
-- (Previously, because of a metavariable instantiation issue, the tactic succeeded as a no-op.)
/-- error: ring_nf made no progress at h -/
#guard_msgs in
example {R : Type*} [CommSemiring R] {x y : R} : True := by
  have h : x + y = 3 := test_sorry
  ring_nf at h

-- Test that `ring_nf` doesn't unfold local let expressions, and `ring_nf!` does
set_option linter.unusedTactic false in
example (x : ℝ) (f : ℝ → ℝ) : True := by
  let y := x
  /-
  Two of these fail, and two of these succeed in rewriting the instance, so it's not a good idea
  to use `fail_if_success` since the instances could change without warning.
  -/
  have : x = y := by
    ring_nf -failIfUnchanged
    ring_nf!
  have : x - y = 0 := by
    ring_nf -failIfUnchanged
    ring_nf!
  have : f x = f y := by
    ring_nf -failIfUnchanged
    ring_nf!
  have : f x - f y = 0 := by
    ring_nf -failIfUnchanged
    ring_nf!
  trivial

-- Test that `ring_nf` doesn't get confused about bound variables
example : (fun x : ℝ => x * x^2) = (fun y => y^2 * y) := by
  ring_nf

-- Test that `ring` works for division without subtraction
example {R : Type} [Semifield R] [CharZero R] {x : R} : x / 2 + x / 2 = x := by ring
