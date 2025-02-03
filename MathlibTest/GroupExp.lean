import Mathlib.Tactic.GroupExp

example (a : G) : a^2*a = a^3 := by group

example (a b c : G) : c*(a*b^2)*((b*b)⁻¹*a⁻¹)*c = c*c := by group

example (a : G) : a^2*a⁻¹*a⁻¹ = 1 := by group

example (n m : ℕ) (a : G) : a^n*a^m = a^(m+n) := by group

example (n : ℤ) (a : G) (h : a^(n*(n+1)-n-n^2) = a) : a = 1 := by
  group at h
  exact h.symm

example (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a := by
  group at h
  rw [h]
  group

-- The next example can be expanded to require an arbitrarily high number of alternations
-- between simp and ring

example (n m : ℤ) (a b : G) : a^(m-n)*b^(m-n)*b^(n-m)*a^(n-m) = 1 := by group

example (n : ℤ) (a b : G) : a^n*b^n*a^n*a^n*a^(-n)*a^(-n)*b^(-n)*a^(-n) = 1 := by group
