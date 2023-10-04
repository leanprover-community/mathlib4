import Mathlib.Tactic.MoveAdd
import Mathlib.Data.Nat.Basic

universe u

section tactic
open Mathlib.MoveAdd

run_cmd if uniquify [ 0,      1,      0,      1,      0,      3] ≠
                    [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (3, 0)] then
          throwError "'uniquify' is not uniquifying"

run_cmd
  let dat := [(0, true), (1, false), (2, true)]
  if (#[0, 1, 2, 3, 4].qsort (fun x y => (weight dat x) ≤ (weight dat y)) != #[0, 2, 3, 4, 1]) then
    throwError "The sorting order induced by 'wtFnc' does not seem to have the required properties"

run_cmd if false = (reorderUsing [0, 1, 2] [(0, false)] = [1, 2, 0] &&
                    reorderUsing [0, 1, 2] [(1, true)] = [1, 0, 2] &&
                    reorderUsing [0, 1, 2] [(1, true), (0, false)] = [1, 2, 0]) then
          throwError "'reorderUsing' is not reordering properly"

run_cmd if reorderUsing [1, 5, 4, 3, 2, 1] [(3, true), (2, false), (1, false)] ≠
                        [3, 5, 4, 1, 2, 1] then
          throwError "'reorderUsing' is not reordering properly"

end tactic

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
