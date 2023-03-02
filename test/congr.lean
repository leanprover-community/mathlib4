import Mathlib.Tactic.Congr!
import Std.Tactic.GuardExpr
import Mathlib.Algebra.Group.Basic

theorem ex1 (a b c : Nat) (h : a = b) : a + c = b + c := by
  congr!

theorem ex2 (a b : Nat) (h : a = b) : ∀ c, a + c = b + c := by
  congr!

theorem ex3 (a b : Nat) (h : a = b) : (fun c => a + c) = (fun c => b + c) := by
  congr!

theorem ex4 (a b : Nat) : Fin (a + b) = Fin (b + a) := by
  congr! 1
  guard_target = a + b = b + a
  apply Nat.add_comm

theorem ex5 : ((a : Nat) → Fin (a + 1)) = ((a : Nat) → Fin (1 + a)) := by
  congr!  2
  rename_i a
  guard_target = a + 1 = 1 + a
  apply Nat.add_comm

theorem ex6 : ((a : Nat) × Fin (a + 1)) = ((a : Nat) × Fin (1 + a)) := by
  congr! 3
  rename_i a
  guard_target = a + 1 = 1 + a
  apply Nat.add_comm

theorem ex7 (p : Prop) (h1 h2 : p) : h1 = h2 := by
  congr!

theorem ex8 (p q : Prop) (h1 : p) (h2 : q) : HEq h1 h2 := by
  congr!

theorem ex9 (a b : Nat) (h : a = b) : a + 1 ≤ b + 1 := by
  congr!

theorem ex10 (x y : Unit) : x = y := by
  congr!

theorem ex11 (p q r : Nat → Prop) (h : q = r) : (∀ n, p n → q n) ↔ (∀ n, p n → r n) := by
  congr!
  rename_i n
  guard_target = q n ↔ r n -- it won't use h itself
  rw [h]
