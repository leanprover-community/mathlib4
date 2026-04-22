module
import Mathlib.Tactic.AddGroup

variable {G : Type} [AddGroup G]

example (a b c : G) : c + (a + b) + (-b + -a) + c = c + c := by add_group

example (a b c : G) : (b + -c) + c + (a + b) + (-b + -a) + c = b + c := by add_group

example (a b c : G) : -c + (b + -c) + c + (a + b) + (-b + -a + -b) + c = 0 := by add_group

-- The following is known as the Hall-Witt identity,
-- see e.g.
-- https://en.wikipedia.org/wiki/Three_subgroups_lemma#Proof_and_the_Hall%E2%80%93Witt_identity
example (g h k : G) :
    g + ⁅⁅-g, h⁆, k⁆ + -g + k + ⁅⁅-k, g⁆, h⁆ + -k + h + ⁅⁅-h, k⁆, g⁆ + -h = 0 := by add_group

example (a : G) : 2 • a + a = 3 • a := by add_group

example (n m : ℕ) (a : G) : n • a + m • a = (n + m) • a := by add_group

example (a b c : G) : c + (a + 2 • b) + (-(b + b) + -a) + c = c + c := by add_group

example (n : ℕ) (a : G) : n • a + n • (-a) = 0 := by add_group

example (a : G) : 2 • a + -a + -a = 0 := by add_group

example (n m : ℕ) (a : G) : n • a + m • a = (m + n) • a := by add_group

example (n : ℕ) (a : G) : (n - n) • a = 0 := by add_group

example (n : ℤ) (a : G) : (n - n) • a = 0 := by add_group

example (n : ℤ) (a : G) (h : (n * (n + 1) - n - n ^ 2) • a = a) : a = 0 := by
  add_group at h
  exact h.symm

example (a b c d : G) (h : c = (a + 2 • b) + (-(b + b) + -a) + d) : a + c + -d = a := by
  add_group at h
  rw [h]
  add_group

-- The next example can be expanded to require an arbitrarily high number of alternations
-- between simp and ring

example (n m : ℤ) (a b : G) : (m - n) • a + (m - n) • b + (n - m) • b + (n - m) • a = 0 := by
  add_group

example (n : ℤ) (a b : G) :
    n • a + n • b + n • a + n • a + (-n) • a + (-n) • a + (-n) • b + (-n) • a = 0 := by add_group

-- Test that add_group deals with `-(0)` properly

example (x y : G) : -((-x) + (x + y) + (-y)) = 0 := by add_group

set_option linter.unusedTactic false in
example (x : G) (h : x = 0) : x = 0 := by
  add_group
  exact h
