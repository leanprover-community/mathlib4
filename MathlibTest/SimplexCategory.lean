import Mathlib.AlgebraicTopology.SimplexCategory
open SimplexCategory.Truncated

variable (n : ℕ) (m : ℕ) (h : m ≤ n)

#guard_expr [2]₃ = (⟨SimplexCategory.mk 2, _⟩ : SimplexCategory.Truncated 3)
#guard_expr [1]ₙ₊₁ = (⟨SimplexCategory.mk 1, _⟩ : SimplexCategory.Truncated (n + 1))
#guard_expr [m]ₙ = (⟨SimplexCategory.mk m, _⟩ : SimplexCategory.Truncated n)

#guard_expr [2, by decide]₃ = (⟨SimplexCategory.mk 2, _⟩ : SimplexCategory.Truncated 3)
#guard_expr [1, by simp]ₙ₊₁ = (⟨SimplexCategory.mk 1, _⟩ : SimplexCategory.Truncated (n + 1))
#guard_expr [m, h]ₙ = (⟨SimplexCategory.mk m, _⟩ : SimplexCategory.Truncated n)

section delaborator

/-- info: [2]₃ : CategoryTheory.FullSubcategory fun a => a.len ≤ 3 -/
#guard_msgs in #check [2]₃

/-- info: [m]ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check [m]ₙ

/-- info: [1]ₙ ₊ ₁ : CategoryTheory.FullSubcategory fun a => a.len ≤ n + 1 -/
#guard_msgs in #check [1]ₙ₊₁

section proofs
set_option pp.proofs true

/-- info: [m,h]ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check [m]ₙ

/-- info: [m,h]ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check [m, h]ₙ

end proofs

end delaborator
