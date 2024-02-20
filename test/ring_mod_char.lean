import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true

-- We deliberately mock ZMod here so that we don't have to import the deps
axiom ZMod (n : ℕ) : Type
@[instance] axiom ZMod.commRing (n : ℕ) : CommRing (ZMod n)
@[instance] axiom ZMod.CharP (n : ℕ) : CharP (ZMod n) n

-- Basic reductions
example : (5 : ZMod 2) = 3 := by ring1 (config := {char := 2})
example (x : ZMod 2) : 3 * x = x := by ring1 (config := {char := 2})
example (x : ZMod 2) : x + x + x = x := by ring1 (config := {char := 2})
example (x : ZMod 2) : 3 • x = x := by ring1 (config := {char := 2})
example (x : ZMod 5) : 4 • x = - x := by ring1 (config := {char := 5})
example (x : ZMod 2) : -x = x := by ring1 (config := {char := 2})
example (x y : ZMod 2) : y - x = x + y := by ring1 (config := {char := 2})
example (x y : ZMod 3) : (x + y) ^ 3 = x ^ 3 + y ^ 3 := by ring (config := {char := 3})
example (x y : ZMod 4) : (x + y) ^ 3 = x ^ 3 + y ^ 3 - (x * y ^ 2 + x ^ 2 * y) := by ring (config := {char := 4})

-- Ensure we don't try to reduce constants in the exponents.
example (x : ZMod 2) : x^4 = x * x * x * x := by ring1 (config := {char := 2})

-- Testcases from the `ring` tactic, ensure the added `char` parameter doesn't break anything.
example (x y : ZMod 3) : x + y = y + x := by ring (config := {char := 3})
example (x y : ZMod 3) : x + y + y = 2 * y + x := by ring (config := {char := 3})
example (x y : ZMod 3) : x + id y = y + id x := by ring! (config := {char := 3})
example {α} [CommRing α] [CharP α 3] (x y : α) : x + y + y - x = 2 * y := by ring (config := {char := 3})
example {α} [CommSemiring α] [CharP α 3] (x y : α) : (x + y)^2 = x^2 + 2 • x * y + y^2 := by ring (config := {char := 3})

example (x y : ZMod 3) : (x + y) ^ 3 = x ^ 3 + y ^ 3 := by ring (config := {char := 3})
example {α} [CommSemiring α] [CharP α 3] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by ring (config := {char := 3})
example (n : ℕ) : (n / 2) + (n / 2) = 2 * (n / 2) := by ring (config := {char := 3})
example {α} [Field α] [CharP α 3] (a : α) : a / 2 = a / 2 := by ring (config := {char := 3})
example {α} [LinearOrderedField α] [CharP α 3] (a b c : α) :
  a * (-c / b) * (-c / b) + -c + c = a * (c / b * (c / b)) := by ring (config := {char := 3})
example {α} [LinearOrderedField α] [CharP α 3] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring (config := {char := 3})
example {α} [CommSemiring α] [CharP α 3] (x : α) : x ^ (2 + 2) = x^4 := by ring1 (config := {char := 3})
example {α} [CommSemiring α] [CharP α 3] (x : α) : x ^ (2 + 2) = x^4 := by ring (config := {char := 3})
example {α} [CommRing α] [CharP α 3] (x : α) : x ^ 2 = x * x := by ring (config := {char := 3})
-- example {α} [CommRing α] [CharP α 3] (x : α) : x ^ (2 : ℤ) = x * x := by ring (config := {char := 3})
example {α} [LinearOrderedField α] [CharP α 3] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring (config := {char := 3})
example {α} [LinearOrderedField α] [CharP α 3] (a b c : α) :
  b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring (config := {char := 3})
example {α} [CommSemiring α] [CharP α 3] (x y z : α) (n : ℕ) :
  (x + y) * (z * (y * y) + (x * x ^ n + (1 + ↑n) * x ^ n * y)) =
  x * (x * x ^ n) + ((2 + ↑n) * (x * x ^ n) * y +
    (x * z + (z * y + (1 + ↑n) * x ^ n)) * (y * y)) := by ring (config := {char := 3})
example {α} [CommRing α] [CharP α 3] (a b c d e : α) :
  (-(a * b) + c + d) * e = (c + (d + -a * b)) * e := by ring (config := {char := 3})
example (a n s : ZMod 3) : a * (n - s) = (n - s) * a := by ring (config := {char := 3})
