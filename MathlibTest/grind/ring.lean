import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Algebra.Order.Field.Defs

/-!
# Preliminary tests for `grind` using Mathlib typeclasses.

These are far from exhaustive tests, for now just testing the minimal functionality for `grind`
using Mathlib's `CommRing` typeclass.
-/

-- We mock ℝ here so that we don't have to import the dependencies.
axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.field : Field ℝ
@[instance] axiom Real.linearOrder : LinearOrder ℝ
@[instance] axiom Real.isStrictOrderedRing : IsStrictOrderedRing ℝ

example (R : Type) [I : Ring R] :
  @AddCommGroup.toGrindIntModule R (@Ring.toAddCommGroup R I) =
    @Lean.Grind.Ring.toIntModule R (@Ring.toGrindRing R I) := rfl

example {α} [CommRing α] (x y : α) : x + y + y - x = 2 * y := by grind
example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by grind
example {α} [CommRing α] (x : α) : x ^ 2 = x * x := by grind
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by grind
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) :
  b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by grind
example {α} [CommRing α] (a b c d e : α) :
  (-(a * b) + c + d) * e = (c + (d + -a * b)) * e := by grind

example {α} [CommRing α] (x y z : α) (h₁ : x^2 = y) (h₂ : x^3 = z) : y^3 = z^2 := by grind
example (x y : ℝ) (h₁ : x^2 = x * y^3) (h₂ : x^3 * y^2 = y) : y^2 = x^4 := by grind
example {α} [CommSemiring α] [IsRightCancelAdd α] (x y z : α) (h : x + z = y + z) : x = y := by
  grind
