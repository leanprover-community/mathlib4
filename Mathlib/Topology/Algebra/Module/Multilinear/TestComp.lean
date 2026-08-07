/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.IsApply

/-! # Test for composition typeclasses -/

@[expose] public section

universe u v w

section Comp

/-- Type class for the `∘ᶠ` notation. -/
class FComp (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ∘ᶠ b` is the composition of `a` and `b`. The meaning of this notation is type-dependent. -/
  protected comp : α → β → γ

@[inherit_doc] infixr:65 " ∘ᶠ " => FComp.comp

/-- `IsCompApply F₁ F₂ F₃ α β γ` states for all `x : α`, `(f ∘ᶠ g) x = f (g x)`. -/
class IsCompApply (F₁ F₂ : Type*) (F₃ α β γ : outParam Type*) [FunLike F₁ β γ] [FunLike F₂ α β]
    [FunLike F₃ α γ] [FComp F₁ F₂ F₃] where
  comp_apply (f : F₁) (g : F₂) (x : α) : (f ∘ᶠ g) x = f (g x)

@[simp, grind =_] alias comp_apply := IsCompApply.comp_apply

end Comp

namespace FunLike

variable {F₁ F₂ F₃ α β γ : Type*}
  [FunLike F₁ β γ] [FunLike F₂ α β] [FunLike F₃ α γ] [FComp F₁ F₂ F₃] [IsCompApply F₁ F₂ F₃ α β γ]

@[norm_cast]
theorem coe_comp (f : F₁) (g : F₂) : ((f ∘ᶠ g) : α → γ) = (f : β → γ) ∘ g := by ext; simp

end FunLike
