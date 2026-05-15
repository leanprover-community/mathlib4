module
import Mathlib.Tactic.Group

open scoped commutatorElement

variable {G : Type} [Group G]

example (a b c : G) : c*(a*b)*(b⁻¹*a⁻¹)*c = c*c := by group

example (a b c : G) : (b*c⁻¹)*c*(a*b)*(b⁻¹*a⁻¹)*c = b*c := by group

example (a b c : G) : c⁻¹*(b*c⁻¹)*c*(a*b)*(b⁻¹*a⁻¹*b⁻¹)*c = 1 := by group

-- The following is known as the Hall-Witt identity,
-- see e.g.
-- https://en.wikipedia.org/wiki/Three_subgroups_lemma#Proof_and_the_Hall%E2%80%93Witt_identity
example (g h k : G) : g*⁅⁅g⁻¹,h⁆,k⁆*g⁻¹*k*⁅⁅k⁻¹,g⁆,h⁆*k⁻¹*h*⁅⁅h⁻¹,k⁆,g⁆*h⁻¹ = 1 := by group

example (a : G) : a^2*a = a^3 := by group

example (n m : ℕ) (a : G) : a^n*a^m = a^(n+m) := by group

example (a b c : G) : c*(a*b^2)*((b*b)⁻¹*a⁻¹)*c = c*c := by group

example (n : ℕ) (a : G) : a^n*(a⁻¹)^n = 1 := by group

example (a : G) : a^2*a⁻¹*a⁻¹ = 1 := by group

example (n m : ℕ) (a : G) : a^n*a^m = a^(m+n) := by group

example (n : ℕ) (a : G) : a^(n-n) = 1 := by group

example (n : ℤ) (a : G) : a^(n-n) = 1 := by group

example (n : ℤ) (a : G) (h : a ^ (n * (n + 1) - n - n ^ 2) = a) : a = 1 := by
  group at h
  exact h.symm

example (a b c d : G) (h : c = (a * b ^ 2) * ((b * b)⁻¹ * a⁻¹) * d) : a*c*d⁻¹ = a := by
  group at h
  rw [h]
  group

-- Test left cancellation
example (a b c : G) (h : a * b = a * c) : b = c := by
  group at h
  guard_hyp h :ₛ b = c
  exact h

-- Test right cancellation
example (a b c : G) (h : b * a = c * a) : b = c := by
  group at h
  guard_hyp h :ₛ b = c
  exact h

-- Tests left and right cancellation in the hypothesis
example (a b c : G) (h : a * b * a = a * c * a) : b = c := by
  group at h
  guard_hyp h :ₛ b = c
  exact h

-- Test converting ( · )^(-1) to ( · )⁻¹ after simplifications and cancellations
example (a b c : G) (h :  b * c * a ^ (- (3 : ℤ)) * a = b * b * a ^ (- (1 : ℤ))) :
    c * a ^ (- (3 : ℤ)) * a = b * a^2 * a ^ (- (3 : ℤ)) := by
  group at h ⊢
  guard_hyp h : c * a ^ (-2 : ℤ) = b * a⁻¹
  exact h

-- Test left and right cancellation and checks that the simplifier does not loop
-- when using associativity in both directions
example (a b c : G) (h : a * (b * a * c) * c = a * (b⁻¹ * (c * a)) * c) :  b * a * c = b⁻¹ * c * a := by
  group at h
  guard_hyp h : b * a * c = b⁻¹ * c * a
  exact h


-- The next example can be expanded to require an arbitrarily high number of alternations
-- between simp and ring
example (n m : ℤ) (a b : G) : a^(m-n)*b^(m-n)*b^(n-m)*a^(n-m) = 1 := by group

example (n : ℤ) (a b : G) : a^n*b^n*a^n*a^(n + 1)*a^(-n - 1)*a^(-n)*b^(-n)*a^(-n) = 1 := by group

-- Test that group deals with `1⁻¹` properly
example (x y : G) : (x⁻¹ * (x * y) * y⁻¹)⁻¹ = 1 := by group

set_option linter.unusedTactic false in
example (x : G) (h : x = 1) : x = 1 := by
  group
  exact h
