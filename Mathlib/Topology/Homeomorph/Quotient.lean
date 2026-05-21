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

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Quot

/-- A homeomorphism `e : X ≃ₜ Y` generates a homeomorphism between quotient spaces,
if `rX x₁ x₂ ↔ rY (e x₁) (e x₂)`. -/
protected def congr {rX : X → X → Prop} {rY : Y → Y → Prop} (e : X ≃ₜ Y)
    (eq : ∀ x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) : Quot rX ≃ₜ Quot rY where
  toEquiv := _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_map (fun x y ↦ by simp [eq]) e.continuous
  continuous_invFun := continuous_quot_map (fun x y ↦ by simp [eq]) e.symm.continuous

/-- Quotient spaces for equal relations are homeomorphic. -/
protected def congrRight {r r' : X → X → Prop} (eq : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) :
    Quot r ≃ₜ Quot r' := Quot.congr (Homeomorph.refl X) eq

/-- A homeomorphism `e : X ≃ₜ Y` generates an equivalence between the quotient space of `X`
by a relation `rX` and the quotient space of `Y` by the image of this relation under `e`. -/
protected def congrLeft {r : X → X → Prop} (e : X ≃ₜ Y) :
    Quot r ≃ₜ Quot fun y₁ y₂ ↦ r (e.symm y₁) (e.symm y₂) :=
  Quot.congr e fun _ _ ↦ by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/-- A homeomorphism `e : X ≃ₜ Y` generates a homeomorphism between quotient spaces,
if `rX x₁ x₂ ↔ rY (e x₁) (e x₂)`. -/
protected def congr {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
    (eq : ∀ x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) :
    Quotient rX ≃ₜ Quotient rY := Quot.congr e eq

/-- Quotient spaces for equal relations are homeomorphic. -/
protected def congrRight {r r' : Setoid X}
    (eq : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) : Quotient r ≃ₜ Quotient r' :=
  Quot.congrRight eq

end Quotient

/-- The quotient by the trivial relation is homeomorphic to the original space. -/
def quotientBot :
    Quotient (⊥ : Setoid X) ≃ₜ X where
  toEquiv := Setoid.quotientBotEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

end Homeomorph
