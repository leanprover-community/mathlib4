/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids with zero.

## Types of morphisms

* `OrderMonoidWithZeroHom`: Ordered monoid with zero homomorphisms.

## Notation

* `→*₀o`: Bundled ordered monoid with zero homs. Also use for group with zero homs.

## TODO

* `≃*₀o`: Bundled ordered monoid with zero isos. Also use for group with zero isos.

## Tags

monoid with zero
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

section MonoidWithZero

variable [Preorder α] [Preorder β] [MulZeroOneClass α] [MulZeroOneClass β]

/-- `OrderMonoidWithZeroHom α β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`OrderMonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parameterize over
`(F : Type*) [FunLike F M N] [MonoidWithZeroHomClass F M N] [OrderHomClass F M N] (f : F)`. -/
structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderMonoidWithZeroHom`. -/
infixr:25 " →*₀o " => OrderMonoidWithZeroHom

section

variable [FunLike F α β]

/-- Turn an element of a type `F`
satisfying `OrderHomClass F α β` and `MonoidWithZeroHomClass F α β`
into an actual `OrderMonoidWithZeroHom`.
This is declared as the default coercion from `F` to `α →+*₀o β`. -/
@[coe]
def OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderHomClass F α β]
    [MonoidWithZeroHomClass F α β] (f : F) : α →*₀o β :=
{ (f : α →*₀ β) with monotone' := OrderHomClass.monotone f }

end

variable [FunLike F α β]

instance [OrderHomClass F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀o β) :=
  ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

end MonoidWithZero

namespace OrderMonoidWithZeroHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

instance : FunLike (α →*₀o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderMonoidWithZeroHom (toFun → apply, -toMonoidWithZeroHom)

instance : MonoidWithZeroHomClass (α →*₀o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'

instance : OrderHomClass (α →*₀o β) α β where
  map_rel f _ _ h := f.monotone' h

-- Other lemmas should be accessed through the `FunLike` API
@[ext]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

theorem toFun_eq_coe (f : α →*₀o β) : f.toFun = (f : α → β) :=
  rfl

@[simp]
theorem coe_mk (f : α →*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α → β) = f :=
  rfl

@[simp]
theorem mk_coe (f : α →*₀o β) (h) : OrderMonoidWithZeroHom.mk (f : α →*₀ β) h = f := rfl

/-- Reinterpret an ordered monoid with zero homomorphism as an order monoid homomorphism. -/
def toOrderMonoidHom (f : α →*₀o β) : α →*o β :=
  { f with }

@[simp]
theorem coe_monoidWithZeroHom (f : α →*₀o β) : ⇑(f : α →*₀ β) = f :=
  rfl

@[simp]
theorem coe_orderMonoidHom (f : α →*₀o β) : ⇑(f : α →*o β) = f :=
  rfl

theorem toOrderMonoidHom_injective : Injective (toOrderMonoidHom : _ → α →*o β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0

theorem toMonoidWithZeroHom_injective : Injective (toMonoidWithZeroHom : _ → α →*₀ β) :=
  fun f g h => ext <| by convert DFunLike.ext_iff.1 h using 0

/-- Copy of an `OrderMonoidWithZeroHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }

@[simp]
theorem coe_copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : α →*₀o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- The identity map as an ordered monoid with zero homomorphism. -/
protected def id : α →*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }

@[simp, norm_cast]
theorem coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id :=
  rfl

instance : Inhabited (α →*₀o α) :=
  ⟨OrderMonoidWithZeroHom.id α⟩

variable {α}

/-- Composition of `OrderMonoidWithZeroHom`s as an `OrderMonoidWithZeroHom`. -/
def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
  { f.toMonoidWithZeroHom.comp (g : α →*₀ β), f.toOrderMonoidHom.comp (g : α →*o β) with }

@[simp]
theorem coe_comp (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

theorem coe_comp_monoidWithZeroHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g :=
  rfl

theorem coe_comp_orderMonoidHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f := rfl

@[simp]
theorem id_comp (f : α →*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f := rfl

@[simp]
theorem cancel_right {g₁ g₂ : β →*₀o γ} {f : α →*₀o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[simp]
theorem cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

section Mul

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
instance : Mul (α →*₀o β) :=
  ⟨fun f g => { (f * g : α →*₀ β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[simp]
theorem coe_mul (f g : α →*₀o β) : ⇑(f * g) = f * g :=
  rfl

@[simp]
theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
  rfl

theorem mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

theorem comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _

end Mul

section LinearOrderedCommMonoidWithZero

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

@[simp]
theorem toMonoidWithZeroHom_eq_coe (f : α →*₀o β) : f.toMonoidWithZeroHom = f := by
  rfl

@[simp]
theorem toMonoidWithZeroHom_mk (f : α →*₀ β) (hf : Monotone f) :
    ((OrderMonoidWithZeroHom.mk f hf) : α →*₀ β) = f := by
  rfl

@[simp]
lemma toMonoidWithZeroHom_coe (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g :=
  rfl

@[simp]
theorem toOrderMonoidHom_eq_coe (f : α →*₀o β) : f.toOrderMonoidHom = f :=
  rfl

@[simp]
lemma toOrderMonoidHom_comp (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl

end LinearOrderedCommMonoidWithZero

end OrderMonoidWithZeroHom

/-- Any ordered group is isomorphic to the units of itself adjoined with `0`. -/
@[simps!]
def OrderMonoidIso.unitsWithZero {α : Type*} [Group α] [Preorder α] : (WithZero α)ˣ ≃*o α where
  toMulEquiv := WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]

/-- A version of `Equiv.optionCongr` for `WithZero` on `OrderMonoidIso`. -/
@[simps!]
def OrderMonoidIso.withZero {G H : Type*}
    [Group G] [PartialOrder G] [Group H] [PartialOrder H] :
    (G ≃*o H) ≃ (WithZero G ≃*o WithZero H) where
  toFun e := ⟨e.toMulEquiv.withZero, fun {a b} ↦ by cases a <;> cases b <;> simp⟩
  invFun e := ⟨MulEquiv.withZero.symm e, fun {a b} ↦ by simp⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

/-- Any linearly ordered group with zero is isomorphic to adjoining `0` to the units of itself. -/
@[simps!]
def OrderMonoidIso.withZeroUnits {α : Type*} [LinearOrderedCommGroupWithZero α]
    [DecidablePred (fun a : α ↦ a = 0)] :
    WithZero αˣ ≃*o α where
  toMulEquiv := WithZero.withZeroUnitsEquiv
  map_le_map_iff' {a b} := by
    cases a <;> cases b <;>
    simp
