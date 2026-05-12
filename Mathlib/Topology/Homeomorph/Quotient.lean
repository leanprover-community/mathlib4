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

/-- An homeomorphism `e : X ≃ₜ Y` generXtes an homeomorphism between quotient spaces,
if `rX a₁ a₂ ↔ rY (e a₁) (e a₂)`. -/
protected def congr {rX : X → X → Prop} {rY : Y → Y → Prop} (e : X ≃ₜ Y)
    (eq : ∀ a₁ a₂, rX a₁ a₂ ↔ rY (e a₁) (e a₂)) : Quot rX ≃ₜ Quot rY where
  toEquiv := _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_map (fun x y ↦ by simp [eq]) e.continuous
  continuous_invFun := continuous_quot_map (fun x y ↦ by simp [eq]) e.symm.continuous

/-- Quotient spaces for equal relations are homeomorphic. -/
protected def congrRight {r r' : X → X → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ₜ Quot r' := Quot.congr (Homeomorph.refl X) eq

/-- An homeomorphism `e : X ≃ₜ Y` generXtes an equivalence between the quotient space of `X`
by a relation `rX` and the quotient space of `Y` by the image of this relation under `e`. -/
protected def congrLeft {r : X → X → Prop} (e : X ≃ₜ Y) :
    Quot r ≃ₜ Quot fun b b' ↦ r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ ↦ by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/-- An homeomorphism `e : X ≃ₜ Y` generXtes an homeomorphism between quotient spaces,
if `rX a₁ a₂ ↔ rY (e a₁) (e a₂)`. -/
protected def congr {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
    (eq : ∀ a₁ a₂, rX a₁ a₂ ↔ rY (e a₁) (e a₂)) :
    Quotient rX ≃ₜ Quotient rY := Quot.congr e eq

/-- Quotient spaces for equal relations are homeomorphic. -/
protected def congrRight {r r' : Setoid X}
    (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quotient r ≃ₜ Quotient r' :=
  Quot.congrRight eq

end Quotient

/-- The quotient by the trivial relation is homeomorphic to the original space. -/
def quotientBot :
    Quotient (⊥ : Setoid X) ≃ₜ X where
  toEquiv := Setoid.quotientBotEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

end Homeomorph
