import Mathlib.AlgebraicTopology.SimplicialObject.Basic

universe u

section Simplicial
open CategoryTheory.SimplicialObject.Truncated

variable (C : Type u) [CategoryTheory.Category.{v} C] (n : ℕ)
  (X : CategoryTheory.SimplicialObject.Truncated C n) (m : ℕ) (h : m ≤ n)

#guard_expr X _[m]ₙ = X.obj (Opposite.op ⟨SimplexCategory.mk m, _⟩)
#guard_expr X _[m, h]ₙ = X.obj (Opposite.op ⟨SimplexCategory.mk m, _⟩)

section delaborator

/-- info: X _[m]ₙ : C -/
#guard_msgs in #check X _[m]ₙ

section proofs
set_option pp.proofs true

/-- info: X _[m,h]ₙ : C -/
#guard_msgs in #check X _[m]ₙ

/-- info: X _[m,h]ₙ : C -/
#guard_msgs in #check X _[m, h]ₙ

end proofs
end delaborator
end Simplicial

section Cosimplicial
open CategoryTheory.CosimplicialObject.Truncated

variable (C : Type u) [CategoryTheory.Category.{v} C] (n : ℕ)
  (X : CategoryTheory.CosimplicialObject.Truncated C n) (m : ℕ) (h : m ≤ n)

#guard_expr X _[m]ₙ = X.obj ⟨SimplexCategory.mk m, _⟩
#guard_expr X _[m, h]ₙ = X.obj ⟨SimplexCategory.mk m, _⟩

section delaborator

/-- info: X _[m]ₙ : C -/
#guard_msgs in #check X _[m]ₙ

section proofs
set_option pp.proofs true

/-- info: X _[m,h]ₙ : C -/
#guard_msgs in #check X _[m]ₙ

/-- info: X _[m,h]ₙ : C -/
#guard_msgs in #check X _[m, h]ₙ

end proofs
end delaborator
end Cosimplicial
