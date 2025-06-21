import Mathlib.AlgebraicTopology.SimplicialObject.Basic

universe u

section Simplicial
open CategoryTheory.SimplicialObject.Truncated

variable (C : Type u) [CategoryTheory.Category.{v} C] (n : ℕ)
  (X : CategoryTheory.SimplicialObject.Truncated C n) (m : ℕ) (h : m ≤ n)

#guard_expr X _⦋m⦌ₙ = X.obj (Opposite.op ⟨SimplexCategory.mk m, _⟩)
#guard_expr X _⦋m, h⦌ₙ = X.obj (Opposite.op ⟨SimplexCategory.mk m, _⟩)

section delaborator

/-- info: X _⦋m⦌ₙ : C -/
#guard_msgs in #check X _⦋m⦌ₙ

/-- info: X _⦋m⦌ₙ : C -/
#guard_msgs in #check X _⦋m⦌ₙ₊₍₃₋₍₂₊₁₎₎

section no_subscript
variable (b : ℕ) (Y: CategoryTheory.SimplicialObject.Truncated C b) (hb : m ≤ b)

/- The delaborator should fail because `b` cannot be subscripted. -/
/-- info: Y.obj (Opposite.op { obj := SimplexCategory.mk m, property := hb }) : C -/
#guard_msgs in #check Y.obj (Opposite.op ⟨SimplexCategory.mk m, hb⟩)

variable {x} (hx : x = X _⦋m⦌ₙ) (n : True)

/- The delaborator should fail because `n` is now shadowed and `✝` cannot be
subscripted. -/
/-- info: hx : x = X.obj (Opposite.op { obj := SimplexCategory.mk m, property := h }) -/
#guard_msgs in #check hx

end no_subscript

section mvars
set_option pp.mvars false

/-- info: X _⦋?_⦌ₙ : C -/
#guard_msgs in #check X _⦋?_, ?_⦌ₙ

/- The delaborator should fail because the truncation level is a metavariable. -/
open CategoryTheory.Functor in
/-- info: (toPrefunctor ?_).obj
(Opposite.op { obj := SimplexCategory.mk ?_, property := ?_ }) : ?_ -/
#guard_msgs in #check Prefunctor.obj
  (toPrefunctor (C := (SimplexCategory.Truncated ?_)ᵒᵖ) ?_)
  ⟨SimplexCategory.mk ?_, ?_⟩

end mvars

section proofs
set_option pp.proofs true

/-- info: X _⦋m,h⦌ₙ : C -/
#guard_msgs in #check X _⦋m, h⦌ₙ

set_option pp.mvars false in
/-- info: X _⦋?_,?_⦌ₙ : C -/
#guard_msgs in #check X _⦋?_, ?_⦌ₙ

end proofs
end delaborator
end Simplicial

section Cosimplicial
open CategoryTheory.CosimplicialObject.Truncated

variable (C : Type u) [CategoryTheory.Category.{v} C] (n : ℕ)
  (X : CategoryTheory.CosimplicialObject.Truncated C n) (m : ℕ) (h : m ≤ n)

#guard_expr X ^⦋m⦌ₙ = X.obj ⟨SimplexCategory.mk m, _⟩
#guard_expr X ^⦋m, h⦌ₙ = X.obj ⟨SimplexCategory.mk m, _⟩

section delaborator

/-- info: X ^⦋m⦌ₙ : C -/
#guard_msgs in #check X ^⦋m⦌ₙ

/-- info: X ^⦋m⦌ₙ : C -/
#guard_msgs in #check X ^⦋m⦌ₙ₊₍₃₋₍₂₊₁₎₎

section no_subscript
variable (b : ℕ) (Y: CategoryTheory.CosimplicialObject.Truncated C b) (hb : m ≤ b)

/- The delaborator should fail because `b` cannot be subscripted. -/
/-- info: Y.obj { obj := SimplexCategory.mk m, property := hb } : C -/
#guard_msgs in #check Y.obj ⟨SimplexCategory.mk m, hb⟩

variable {x} (hx : x = X ^⦋m⦌ₙ) (n : True)

/- The delaborator should fail because `n` is now shadowed and `✝` cannot be
subscripted. -/
/-- info: hx : x = X.obj { obj := SimplexCategory.mk m, property := h } -/
#guard_msgs in #check hx

end no_subscript

section mvars
set_option pp.mvars false

/-- info: X ^⦋?_⦌ₙ : C -/
#guard_msgs in #check X ^⦋?_, ?_⦌ₙ

/- The delaborator should fail because the truncation level is a metavariable. -/
open CategoryTheory.Functor in
/-- info: (toPrefunctor ?_).obj { obj := SimplexCategory.mk ?_, property := ?_ } : ?_ -/
#guard_msgs in #check Prefunctor.obj
  (toPrefunctor (C := SimplexCategory.Truncated ?_) ?_) ⟨SimplexCategory.mk ?_, ?_⟩

end mvars

section proofs
set_option pp.proofs true

/-- info: X ^⦋m,h⦌ₙ : C -/
#guard_msgs in #check X ^⦋m, h⦌ₙ

set_option pp.mvars false in
/-- info: X ^⦋?_,?_⦌ₙ : C -/
#guard_msgs in #check X ^⦋?_, ?_⦌ₙ

end proofs
end delaborator
end Cosimplicial
