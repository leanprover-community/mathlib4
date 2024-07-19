/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Lemmas about `Sigma` from Lean 3 core.
-/

universe u v

theorem ex_of_psig {α : Sort u} {p : α → Prop} : (Σ' x, p x) → ∃ x, p x
  | ⟨x, hx⟩ => ⟨x, hx⟩

protected theorem Sigma.eq {α : Type u} {β : α → Type v} : ∀ {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl

protected theorem PSigma.eq {α : Sort u} {β : α → Sort v} : ∀ {p₁ p₂ : Σ' a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl
