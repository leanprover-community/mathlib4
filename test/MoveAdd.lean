import Mathlib.Tactic.MoveAdd
import Mathlib.Data.Nat.Basic

universe u

variable {R : Type u}
section add

section semigroup
variable [AddCommSemigroup R] {a b c d e f g h : R}

example (h : a + b + c = d) : b + (a + c) = d := by
  move_add [← a]
  assumption

example : let k := c + (a + b); k = a + b + c := by
  move_add [← a, c]
  rfl

example (h : b + a = b + c + a) : a + b = a + b + c :=
by move_add [a]; assumption

example [Mul R] [Neg R] : a + (b + c + a) * (- (d + e) + e) + f + g =
    (c + b + a) * (e + - (e + d)) + g + f + a := by
  move_add [b, d, g, f, a, e]; rfl

example (h : d + b + a = b + a → d + c + a = c + a) : a + d + b = b + a → d + c + a = a + c := by
  move_add [a]
  assumption

example [DecidableEq R] : if b + a = c + a then a + b = c + a else a + b ≠ c + a := by
  move_add [← a]
  split_ifs with h <;>
  exact h

example (h : a + c + b = a + d + b) : c + b + a = b + a + d := by
  move_add [← a, b]  -- Goal before `exact h`: `a + c + b = a + d + b`
  exact h

example [Mul R] (h : a * c + c + b * c = a * d + d + b * d) :
    c + b * c + a * c = a * d + d + b * d := by
  -- the first input `_ * c` unifies with `b * c` and moves to the right
  -- the second input `_ * c` unifies with `a * c` and moves to the left
  move_add [_ * c, ← _ * c] -- Goal before `exact h`: `a * c + c + b * c = a * d + d + b * d`
  exact h

end semigroup
variable [AddCommMonoidWithOne R] [Mul R] {f g h X r s t u : R} (C D E : R → R)

example (he : E (C r * D X + D X * h + 7 + 42 + f) = C r * D X + h * D X + 7 + 42 + g) :
    E (7 + f + (C r * D X + 42) + D X * h) = C r * D X + h * D X + g + 7 + 42 := by
  -- move `7, 42, f, g` to the right of their respective sides
  move_add [(7 : R), (42 : R), f, g]
  assumption

end add

example [CommSemigroup R] (a b c d : R) (h : a * b * c = d) : b * (a * c) = d := by
  move_mul [← a]
  assumption

example (a b : ℕ) : a + max a b = max b a + a := by
  move_oper (max 0 0) [← a]
  move_oper (0 + 0) [a]
  rfl

example {R : Type u} [CommSemigroup R] {a b : R} :
    ∀ x : R, ∃ y : R, a * x * b * y = x * y * b * a := by
  move_mul [a, b]
  exact fun x ↦ ⟨x, rfl⟩

example {R : Type u} [Add R] [CommSemigroup R] {a b c d e f g : R} :
    a * (b * c * a) * ((d * e) * e) * f * g = (c * b * a) * (e * (e * d)) * g * f * a := by
  move_mul [a, a, b, c, d, e, f]
  rfl
