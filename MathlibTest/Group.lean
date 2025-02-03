import Mathlib.Tactic.Group

variable {G : Type} [Group G]

example (a b c : G) : c*(a*b)*(b⁻¹*a⁻¹)*c = c*c := by group

example (a b c : G) : (b*c⁻¹)*c*(a*b)*(b⁻¹*a⁻¹)*c = b*c := by group

example (a b c : G) : c⁻¹*(b*c⁻¹)*c*(a*b)*(b⁻¹*a⁻¹*b⁻¹)*c = 1 := by group

-- The following is known as the Hall-Witt identity,
-- see e.g.
-- https://en.wikipedia.org/wiki/Three_subgroups_lemma#Proof_and_the_Hall%E2%80%93Witt_identity
example (g h k : G) : g*⁅⁅g⁻¹,h⁆,k⁆*g⁻¹*k*⁅⁅k⁻¹,g⁆,h⁆*k⁻¹*h*⁅⁅h⁻¹,k⁆,g⁆*h⁻¹ = 1 := by group

example (n m : ℕ) (a : G) : a^n*a^m = a^(n+m) := by group

example (n : ℕ) (a : G) : a^n*(a⁻¹)^n = 1 := by group

example (n : ℕ) (a : G) : a^(n-n) = 1 := by group

example (n : ℤ) (a : G) : a^(n-n) = 1 := by group

-- Test that group deals with `1⁻¹` properly

example (x y : G) : (x⁻¹ * (x * y) * y⁻¹)⁻¹ = 1 := by group

set_option linter.unusedTactic false in
example (x : G) (h : x = 1) : x = 1 := by
  group
  exact h
