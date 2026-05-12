/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms between quotient spaces
-/

@[expose] public section

namespace Homeomorph

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace Quot

/-- An homeomorphism `e : α ≃ₜ β` generates an homeomorphism between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ₜ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ₜ Quot rb where
  toEquiv := _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_map (fun x y ↦ by simp [eq]) e.continuous
  continuous_invFun := continuous_quot_map (fun x y ↦ by simp [eq]) e.symm.continuous

/-- Quotient spaces for equal relations are homeomorphic. -/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ₜ Quot r' := Quot.congr (Homeomorph.refl α) eq

/-- An homeomorphism `e : α ≃ₜ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congrLeft {r : α → α → Prop} (e : α ≃ₜ β) :
    Quot r ≃ₜ Quot fun b b' => r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/-- An homeomorphism `e : α ≃ₜ β` generates an homeomorphism between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ₜ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    Quotient ra ≃ₜ Quotient rb := Quot.congr e eq

/-- Quotient spaces for equal relations are homeomorphic. -/
protected def congrRight {r r' : Setoid α}
    (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quotient r ≃ₜ Quotient r' :=
  Quot.congrRight eq

end Quotient

/-- The quotient by the trivial relation is homeomorphic to the original space. -/
def quotientBot :
    Quotient (⊥ : Setoid α) ≃ₜ α where
  toEquiv := Setoid.quotientBotEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

end Homeomorph
