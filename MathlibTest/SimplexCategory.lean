import Mathlib.Tactic.SimplexCategory
open SimplexCategory.Truncated

variable (n : ℕ) (m : ℕ) (h : m ≤ n)

#guard_expr ⦋2⦌₃ = (⟨SimplexCategory.mk 2, _⟩ : SimplexCategory.Truncated 3)
#guard_expr ⦋1⦌ₙ₊₁ = (⟨SimplexCategory.mk 1, _⟩ : SimplexCategory.Truncated (n + 1))
#guard_expr ⦋m⦌ₙ = (⟨SimplexCategory.mk m, _⟩ : SimplexCategory.Truncated n)

#guard_expr ⦋2, by decide⦌₃ = (⟨SimplexCategory.mk 2, _⟩ : SimplexCategory.Truncated 3)
#guard_expr ⦋1, by simp⦌ₙ₊₁ = (⟨SimplexCategory.mk 1, _⟩ : SimplexCategory.Truncated (n + 1))
#guard_expr ⦋m, h⦌ₙ = (⟨SimplexCategory.mk m, _⟩ : SimplexCategory.Truncated n)

section delaborator

/-- info: ⦋2⦌₃ : CategoryTheory.FullSubcategory fun a => a.len ≤ 3 -/
#guard_msgs in #check ⦋2⦌₃

/-- info: ⦋m⦌ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check ⦋m⦌ₙ

/-- info: ⦋m⦌ₙ ₊ ₁ : CategoryTheory.FullSubcategory fun a => a.len ≤ n + 1 -/
#guard_msgs in #check ⦋m⦌ₙ ₊ ₁

/-- info: ⦋m⦌ₙ ₊ ₍₄ ₋ ₍₂ ₊ ₁₎₎ :
CategoryTheory.FullSubcategory fun a => a.len ≤ n + (4 - (2 + 1)) -/
#guard_msgs in #check ⦋m⦌ₙ ₊ ₍₄ ₋ ₍₂ ₊ ₁₎₎

section no_subscript
variable (b : ℕ) (hb : m ≤ b)

/- The delaborator should fail because `b` cannot be subscripted. -/
/-- info: { obj := SimplexCategory.mk m, property := hb } :
CategoryTheory.FullSubcategory fun a => a.len ≤ b -/
#guard_msgs in
#check (⟨SimplexCategory.mk m, hb⟩ : SimplexCategory.Truncated b)

variable {x} (hx : x = ⦋m⦌ₙ) (n : True)

/- The delaborator should fail because `n` is now shadowed and `✝` cannot be
subscripted. -/
/-- info: hx : x = { obj := SimplexCategory.mk m, property := h } -/
#guard_msgs in #check hx

end no_subscript

section mvars
set_option pp.mvars false

/-- info: ⦋?_⦌ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check ⦋?_, ?_⦌ₙ

/- The delaborator should fail because the truncation level is a metavariable. -/
/-- info: { obj := SimplexCategory.mk ?_, property := ?_ } :
CategoryTheory.FullSubcategory fun a => a.len ≤ ?_ -/
#guard_msgs in #check @CategoryTheory.FullSubcategory.mk
  SimplexCategory (fun a ↦ a.len ≤ ?_) (SimplexCategory.mk ?_) ?_

end mvars

section proofs
set_option pp.proofs true

/-- info: ⦋m,h⦌ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check ⦋m, h⦌ₙ

set_option pp.mvars false in
/-- info: ⦋?_,?_⦌ₙ : CategoryTheory.FullSubcategory fun a => a.len ≤ n -/
#guard_msgs in #check ⦋?_, ?_⦌ₙ

end proofs

end delaborator
