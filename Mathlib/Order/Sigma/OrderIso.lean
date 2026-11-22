/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Sigma

/-!
-/

/-! ### Order isomorphisms -/

@[expose] public section

open Sigma Lex

namespace OrderIso

/-- An equivalence `f : α₁ ≃o α₂` generates an equivalence between `Σₗ a, β (f a)` and
`Σₗ a, β a`. -/
@[simps! (attr := grind =) apply]
def sigmaCongrLeft {α₁ α₂ : Type*} {β : α₂ → Type*}
    [Preorder α₁] [Preorder α₂] [∀ a, Preorder (β a)] (e : α₁ ≃o α₂) :
    (Σₗ a : α₁, β (e a)) ≃o Σₗ a : α₂, β a where
  map_rel_iff' := by
    simp_rw [Lex.forall]
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    constructor <;>
    · intro h
      rw [Sigma.Lex.le_def] at h
      obtain h | ⟨heq, h⟩ := h
      · exact left _ _ (by simpa using h)
      · obtain rfl : a₁ = a₂ := by simpa using heq
        exact right _ _ h
  __ := ofLex.trans <| (Equiv.sigmaCongrLeft e.toEquiv).trans toLex

/-- A family of equivalences `∀ a, β₁ a ≃o β₂ a` generates an equivalence between `Σₗ a, β₁ a` and
`Σₗ a, β₂ a`. -/
@[simps! (attr := grind =) apply]
def sigmaCongrRight {α} {β₁ β₂ : α → Type*} [Preorder α]
    [∀ a, Preorder (β₁ a)] [∀ a, Preorder (β₂ a)] (F : ∀ a, β₁ a ≃o β₂ a) :
    (Σₗ a, β₁ a) ≃o Σₗ a, β₂ a where
  map_rel_iff' := by
    simp_rw [Lex.forall]
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    constructor
    · intro h
      cases h with
      | left _ _ h => exact left _ _ h
      | right _ _ h => exact right _ _ ((F a₁).le_iff_le.1 h)
    · intro h
      cases h with
      | left _ _ h => exact left _ _ h
      | right _ _ h => exact right _ _ ((F a₁).le_iff_le.2 h)
  __ := ofLex.trans <| (Equiv.sigmaCongrRight (fun a ↦ F a)).trans toLex

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*} [Preorder α₁] [Preorder α₂]
    (f : α₁ ≃o α₂) [∀ a, Preorder (β₁ a)] [∀ a, Preorder (β₂ a)] (F : ∀ a, β₁ a ≃o β₂ (f a)) :
    (Σₗ a, β₁ a) ≃o Σₗ a, β₂ a :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)

/-- `Sigma` type with a constant fiber is equivalent to the product. -/
@[simps! (attr := mfld_simps, grind =) apply symm_apply]
def sigmaEquivProd (α β : Type*) [Preorder α] [Preorder β] : (Σₗ _ : α, β) ≃o α ×ₗ β where
  map_rel_iff' := by simp [Sigma.Lex.le_def, Prod.Lex.le_iff]
  __ := ofLex.trans <| (Equiv.sigmaEquivProd α β).trans toLex

end OrderIso
