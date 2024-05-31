import Mathlib.Tactic.MoveAdd
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.Ring.Nat

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

example (h : b + a = b + c + a) : a + b = a + b + c := by
  move_add [a]; assumption

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

section mul
example [CommSemigroup R] (a b c d : R) (h : a * b * c = d) : b * (a * c) = d := by
  move_mul [← a]
  assumption

example (a b : ℕ) : a + max a b = max b a + a := by
  move_oper Max.max [← a]
  move_oper HAdd.hAdd [a]
  rfl

example {R : Type u} [CommSemigroup R] {a b : R} :
    ∀ x : R, ∃ y : R, a * x * b * y = x * y * b * a := by
  move_mul [a, b]
  exact fun x ↦ ⟨x, rfl⟩

example {R : Type u} [Add R] [CommSemigroup R] {a b c d e f g : R} :
    a * (b * c * a) * ((d * e) * e) * f * g = (c * b * a) * (e * (e * d)) * g * f * a := by
  move_mul [a, a, b, c, d, e, f]
  rfl

/-
#  Sample usage of `move_oper`
-/

example (a b c : Prop) : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  move_oper And [a]
  rfl

example (a b c : Prop) : a ∨ b ∨ c ↔ b ∨ c ∨ a := by
  move_oper Or [a]
  rfl

example {R} [LinearOrder R] (a b c : R) : max (max a b) c = max (max b c) a := by
  move_oper Max.max [a]
  rfl

example {R} [LinearOrder R] (a b c : R) : min (min a b) c = min (min b c) a := by
  move_oper Min.min [a]
  rfl
end mul

section left_assoc

example {a b c d e : Prop} (h : a ∧ b ∧ c ∧ d ∧ e) : a ∧ c ∧ e ∧ b ∧ d := by
  move_oper And [a, b, c, d, e]
  exact h

example {a b c d e : Prop} (h : a ∨ b ∨ c ∨ d ∨ e) : a ∨ c ∨ e ∨ b ∨ d := by
  move_oper Or [a, b, c, d, e]
  exact h

end left_assoc

-- Adaptation note: nightly-2024-03-11
-- This test is now failing with `unknown free variable '_fvar.36787'`
-- example (k : ℕ) (h0 : 0 + 2 = 9 + 0) (h9 : k + 2 = k + 9) : k + 2 = 9 + k := by
--   induction' k with k _ih
--   · exact h0
--   · move_add [9]
--     exact h9

-- Testing internals of the tactic `move_add`.
section tactic
open Mathlib.MoveAdd

#guard (uniquify [ 0,      1,      0,      1,      0,      3] =
                 [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (3, 0)])

#guard
  (let dat := [(0, true), (1, false), (2, true)]
   #[0, 1, 2, 3, 4].qsort (weight dat · ≤ weight dat ·) = #[0, 2, 3, 4, 1])

#guard false = ( reorderUsing [0, 1, 2] [(0, false)] = [1, 2, 0] &&
                 reorderUsing [0, 1, 2] [(1, true)] = [1, 0, 2] &&
                 reorderUsing [0, 1, 2] [(1, true), (0, false)] != [1, 2, 0])

#guard reorderUsing [1, 5, 4, 3, 2, 1] [(3, true), (2, false), (1, false)] =
                        [3, 5, 4, 1, 2, 1]

end tactic
