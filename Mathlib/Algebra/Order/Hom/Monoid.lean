/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Pi.Algebra
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.Monoid.WithZero.Defs
import Mathlib.Order.Hom.Basic

#align_import algebra.order.hom.monoid from "leanprover-community/mathlib"@"3342d1b2178381196f818146ff79bc0e7ccd9e2d"

/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids.

## Types of morphisms

* `OrderAddMonoidHom`: Ordered additive monoid homomorphisms.
* `OrderMonoidHom`: Ordered monoid homomorphisms.
* `OrderMonoidWithZeroHom`: Ordered monoid with zero homomorphisms.

## Typeclasses

* `OrderAddMonoidHomClass`
* `OrderMonoidHomClass`
* `OrderMonoidWithZeroHomClass`

## Notation

* `→+o`: Bundled ordered additive monoid homs. Also use for additive groups homs.
* `→*o`: Bundled ordered monoid homs. Also use for groups homs.
* `→*₀o`: Bundled ordered monoid with zero homs. Also use for groups with zero homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom as
a function via this coercion.

There is no `OrderGroupHom` -- the idea is that `OrderMonoidHom` is used.
The constructor for `OrderMonoidHom` needs a proof of `map_one` as well as `map_mul`; a separate
constructor `OrderMonoidHom.mk'` will construct ordered group homs (i.e. ordered monoid homs
between ordered groups) given only a proof that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `OrderMonoidHom`. When
they can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

ordered monoid, ordered group, monoid with zero
-/


open Function

variable {F α β γ δ : Type*}

section AddMonoid

/-- `α →+o β` is the type of monotone functions `α → β` that preserve the `OrderedAddCommMonoid`
structure.

`OrderAddMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+o β)`,
you should parametrize over `(F : Type*) [OrderAddMonoidHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderAddMonoidHomClass`. -/
structure OrderAddMonoidHom (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α →+ β where
  /-- An `OrderAddMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_add_monoid_hom OrderAddMonoidHom

/-- Infix notation for `OrderAddMonoidHom`. -/
infixr:25 " →+o " => OrderAddMonoidHom

section

/-- `OrderAddMonoidHomClass F α β` states that `F` is a type of ordered monoid homomorphisms.

You should also extend this typeclass when you extend `OrderAddMonoidHom`. -/
class OrderAddMonoidHomClass (F : Type*) (α β : outParam <| Type*) [Preorder α] [Preorder β]
  [AddZeroClass α] [AddZeroClass β] extends AddMonoidHomClass F α β where
  /-- An `OrderAddMonoidHom` is a monotone function. -/
  monotone (f : F) : Monotone f
#align order_add_monoid_hom_class OrderAddMonoidHomClass

end

-- Instances and lemmas are defined below through `@[to_additive]`.
end AddMonoid

section Monoid

/-- `α →*o β` is the type of functions `α → β` that preserve the `OrderedCommMonoid` structure.

`OrderMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*o β)`,
you should parametrize over `(F : Type*) [OrderMonoidHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderMonoidHomClass`. -/
@[to_additive]
structure OrderMonoidHom (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends α →* β where
  /-- An `OrderMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_monoid_hom OrderMonoidHom

/-- Infix notation for `OrderMonoidHom`. -/
infixr:25 " →*o " => OrderMonoidHom

section

/-- `OrderMonoidHomClass F α β` states that `F` is a type of ordered monoid homomorphisms.

You should also extend this typeclass when you extend `OrderMonoidHom`. -/
@[to_additive]
class OrderMonoidHomClass (F : Type*) (α β : outParam <| Type*) [Preorder α] [Preorder β]
  [MulOneClass α] [MulOneClass β] extends MonoidHomClass F α β where
  /-- An `OrderMonoidHom` is a monotone function. -/
  monotone (f : F) : Monotone f
#align order_monoid_hom_class OrderMonoidHomClass

end

variable {_ : Preorder α} {_ : Preorder β} {_ : MulOneClass α} {_ : MulOneClass β}

/-- Turn an element of a type `F` satisfying `OrderMonoidHomClass F α β` into an actual
`OrderMonoidHom`. This is declared as the default coercion from `F` to `α →*o β`. -/
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `OrderAddMonoidHomClass F α β` into an actual
  `OrderAddMonoidHom`. This is declared as the default coercion from `F` to `α →+o β`."]
def OrderMonoidHomClass.toOrderMonoidHom [OrderMonoidHomClass F α β] (f : F) : α →*o β :=
  { (f : α →* β) with monotone' := monotone f }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderMonoidHomClass.toOrderHomClass [OrderMonoidHomClass F α β] :
    OrderHomClass F α β :=
  { ‹OrderMonoidHomClass F α β› with map_rel := OrderMonoidHomClass.monotone }
#align order_monoid_hom_class.to_order_hom_class OrderMonoidHomClass.toOrderHomClass
#align order_add_monoid_hom_class.to_order_hom_class OrderAddMonoidHomClass.toOrderHomClass

/-- Any type satisfying `OrderMonoidHomClass` can be cast into `OrderMonoidHom` via
  `OrderMonoidHomClass.toOrderMonoidHom`. -/
@[to_additive "Any type satisfying `OrderAddMonoidHomClass` can be cast into `OrderAddMonoidHom` via
  `OrderAddMonoidHomClass.toOrderAddMonoidHom`"]
instance [OrderMonoidHomClass F α β] : CoeTC F (α →*o β) :=
  ⟨OrderMonoidHomClass.toOrderMonoidHom⟩

end Monoid

section MonoidWithZero

variable [Preorder α] [Preorder β] [MulZeroOneClass α] [MulZeroOneClass β]

/-- `OrderMonoidWithZeroHom α β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`OrderMonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parametrize over `(F : Type*) [OrderMonoidWithZeroHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderMonoidWithZeroHomClass`. -/
structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone' : Monotone toFun
#align order_monoid_with_zero_hom OrderMonoidWithZeroHom

/-- Infix notation for `OrderMonoidWithZeroHom`. -/
infixr:25 " →*₀o " => OrderMonoidWithZeroHom

section

/-- `OrderMonoidWithZeroHomClass F α β` states that `F` is a type of
ordered monoid with zero homomorphisms.

You should also extend this typeclass when you extend `OrderMonoidWithZeroHom`. -/
class OrderMonoidWithZeroHomClass (F : Type*) (α β : outParam <| Type*) [Preorder α] [Preorder β]
  [MulZeroOneClass α] [MulZeroOneClass β] extends MonoidWithZeroHomClass F α β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone (f : F) : Monotone f
#align order_monoid_with_zero_hom_class OrderMonoidWithZeroHomClass

/-- Turn an element of a type `F` satisfying `OrderMonoidWithZeroHomClass F α β` into an actual
`OrderMonoidWithZeroHom`. This is declared as the default coercion from `F` to `α →+*₀o β`. -/
@[coe]
def OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderMonoidWithZeroHomClass F α β]
    (f : F) : α →*₀o β :=
{ (f : α →*₀ β) with monotone' := monotone f }

end

-- See note [lower instance priority]
instance (priority := 100) OrderMonoidWithZeroHomClass.toOrderMonoidHomClass
    {_ : Preorder α} {_ : Preorder β} {_ : MulZeroOneClass α} {_ : MulZeroOneClass β}
    [OrderMonoidWithZeroHomClass F α β] : OrderMonoidHomClass F α β :=
  { ‹OrderMonoidWithZeroHomClass F α β› with }
#align order_monoid_with_zero_hom_class.to_order_monoid_hom_class OrderMonoidWithZeroHomClass.toOrderMonoidHomClass

instance [OrderMonoidWithZeroHomClass F α β] : CoeTC F (α →*₀o β) :=
  ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

end MonoidWithZero

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] [OrderedAddCommMonoid β] [OrderAddMonoidHomClass F α β] (f : F)
  {a : α}

theorem map_nonneg (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [← map_zero f]
  -- ⊢ ↑f 0 ≤ ↑f a
  exact OrderHomClass.mono _ ha
  -- 🎉 no goals
#align map_nonneg map_nonneg

theorem map_nonpos (ha : a ≤ 0) : f a ≤ 0 := by
  rw [← map_zero f]
  -- ⊢ ↑f a ≤ ↑f 0
  exact OrderHomClass.mono _ ha
  -- 🎉 no goals
#align map_nonpos map_nonpos

end OrderedAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] [OrderedAddCommMonoid β] [AddMonoidHomClass F α β] (f : F)

theorem monotone_iff_map_nonneg : Monotone (f : α → β) ↔ ∀ a, 0 ≤ a → 0 ≤ f a :=
  ⟨fun h a => by
    rw [← map_zero f]
    -- ⊢ 0 ≤ a → ↑f 0 ≤ ↑f a
    apply h, fun h a b hl => by
    -- 🎉 no goals
    rw [← sub_add_cancel b a, map_add f]
    -- ⊢ ↑f a ≤ ↑f (b - a) + ↑f a
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩
    -- 🎉 no goals
#align monotone_iff_map_nonneg monotone_iff_map_nonneg

theorem antitone_iff_map_nonpos : Antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 :=
  monotone_toDual_comp_iff.symm.trans <| monotone_iff_map_nonneg _
#align antitone_iff_map_nonpos antitone_iff_map_nonpos

theorem monotone_iff_map_nonpos : Monotone (f : α → β) ↔ ∀ a ≤ 0, f a ≤ 0 :=
  antitone_comp_ofDual_iff.symm.trans <| antitone_iff_map_nonpos _
#align monotone_iff_map_nonpos monotone_iff_map_nonpos

theorem antitone_iff_map_nonneg : Antitone (f : α → β) ↔ ∀ a ≤ 0, 0 ≤ f a :=
  monotone_comp_ofDual_iff.symm.trans <| monotone_iff_map_nonneg _
#align antitone_iff_map_nonneg antitone_iff_map_nonneg

variable [CovariantClass β β (· + ·) (· < ·)]

theorem strictMono_iff_map_pos : StrictMono (f : α → β) ↔ ∀ a, 0 < a → 0 < f a := by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  -- ⊢ 0 < a → 0 < ↑f a
  · rw [← map_zero f]
    -- ⊢ 0 < a → ↑f 0 < ↑f a
    apply h
    -- 🎉 no goals
  · rw [← sub_add_cancel b a, map_add f]
    -- ⊢ ↑f a < ↑f (b - a) + ↑f a
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)
    -- 🎉 no goals
#align strict_mono_iff_map_pos strictMono_iff_map_pos

theorem strictAnti_iff_map_neg : StrictAnti (f : α → β) ↔ ∀ a, 0 < a → f a < 0 :=
  strictMono_toDual_comp_iff.symm.trans <| strictMono_iff_map_pos _
#align strict_anti_iff_map_neg strictAnti_iff_map_neg

theorem strictMono_iff_map_neg : StrictMono (f : α → β) ↔ ∀ a < 0, f a < 0 :=
  strictAnti_comp_ofDual_iff.symm.trans <| strictAnti_iff_map_neg _
#align strict_mono_iff_map_neg strictMono_iff_map_neg

theorem strictAnti_iff_map_pos : StrictAnti (f : α → β) ↔ ∀ a < 0, 0 < f a :=
  strictMono_comp_ofDual_iff.symm.trans <| strictMono_iff_map_pos _
#align strict_anti_iff_map_pos strictAnti_iff_map_pos

end OrderedAddCommGroup

namespace OrderMonoidHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

@[to_additive]
 instance : OrderMonoidHomClass (α →*o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    -- ⊢ { toMonoidHom := { toOneHom := { toFun := toFun✝, map_one' := map_one'✝ }, m …
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    -- ⊢ { toMonoidHom := { toOneHom := { toFun := toFun✝¹, map_one' := map_one'✝¹ }, …
    congr
    -- 🎉 no goals
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  monotone f := f.monotone'

-- Porting note:
-- These helper instances are unhelpful in Lean 4, so omitting:
-- /-- Helper instance for when there's too many metavariables to apply `FunLike.instCoeFunForAll`
-- directly. -/
-- @[to_additive "Helper instance for when there's too many metavariables to apply
-- `FunLike.instCoeFunForAll` directly."]
-- instance : CoeFun (α →*o β) fun _ => α → β :=
--   FunLike.instCoeFunForAll

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align order_monoid_hom.ext OrderMonoidHom.ext
#align order_add_monoid_hom.ext OrderAddMonoidHom.ext

@[to_additive]
theorem toFun_eq_coe (f : α →*o β) : f.toFun = (f : α → β) :=
  rfl
#align order_monoid_hom.to_fun_eq_coe OrderMonoidHom.toFun_eq_coe
#align order_add_monoid_hom.to_fun_eq_coe OrderAddMonoidHom.toFun_eq_coe

@[to_additive (attr := simp)]
theorem coe_mk (f : α →* β) (h) : (OrderMonoidHom.mk f h : α → β) = f :=
  rfl
#align order_monoid_hom.coe_mk OrderMonoidHom.coe_mk
#align order_add_monoid_hom.coe_mk OrderAddMonoidHom.coe_mk

@[to_additive (attr := simp)]
theorem mk_coe (f : α →*o β) (h) : OrderMonoidHom.mk (f : α →* β) h = f := by
  ext
  -- ⊢ ↑{ toMonoidHom := ↑f, monotone' := h } a✝ = ↑f a✝
  rfl
  -- 🎉 no goals
#align order_monoid_hom.mk_coe OrderMonoidHom.mk_coe
#align order_add_monoid_hom.mk_coe OrderAddMonoidHom.mk_coe

/-- Reinterpret an ordered monoid homomorphism as an order homomorphism. -/
@[to_additive "Reinterpret an ordered additive monoid homomorphism as an order homomorphism."]
def toOrderHom (f : α →*o β) : α →o β :=
  { f with }
#align order_monoid_hom.to_order_hom OrderMonoidHom.toOrderHom
#align order_add_monoid_hom.to_order_hom OrderAddMonoidHom.toOrderHom

@[to_additive (attr := simp)]
theorem coe_monoidHom (f : α →*o β) : ((f : α →* β) : α → β) = f :=
  rfl
#align order_monoid_hom.coe_monoid_hom OrderMonoidHom.coe_monoidHom
#align order_add_monoid_hom.coe_add_monoid_hom OrderAddMonoidHom.coe_addMonoidHom

@[to_additive (attr := simp)]
theorem coe_orderHom (f : α →*o β) : ((f : α →o β) : α → β) = f :=
  rfl
#align order_monoid_hom.coe_order_hom OrderMonoidHom.coe_orderHom
#align order_add_monoid_hom.coe_order_hom OrderAddMonoidHom.coe_orderHom

@[to_additive]
theorem toMonoidHom_injective : Injective (toMonoidHom : _ → α →* β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h using 0
            -- 🎉 no goals
#align order_monoid_hom.to_monoid_hom_injective OrderMonoidHom.toMonoidHom_injective
#align order_add_monoid_hom.to_add_monoid_hom_injective OrderAddMonoidHom.toAddMonoidHom_injective

@[to_additive]
theorem toOrderHom_injective : Injective (toOrderHom : _ → α →o β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h using 0
            -- 🎉 no goals
#align order_monoid_hom.to_order_hom_injective OrderMonoidHom.toOrderHom_injective
#align order_add_monoid_hom.to_order_hom_injective OrderAddMonoidHom.toOrderHom_injective

/-- Copy of an `OrderMonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive "Copy of an `OrderAddMonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities."]
protected def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }
#align order_monoid_hom.copy OrderMonoidHom.copy
#align order_add_monoid_hom.copy OrderAddMonoidHom.copy

@[to_additive (attr := simp)]
theorem coe_copy (f : α →*o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align order_monoid_hom.coe_copy OrderMonoidHom.coe_copy
#align order_add_monoid_hom.coe_copy OrderAddMonoidHom.coe_copy

@[to_additive]
theorem copy_eq (f : α →*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align order_monoid_hom.copy_eq OrderMonoidHom.copy_eq
#align order_add_monoid_hom.copy_eq OrderAddMonoidHom.copy_eq

variable (α)

/-- The identity map as an ordered monoid homomorphism. -/
@[to_additive "The identity map as an ordered additive monoid homomorphism."]
protected def id : α →*o α :=
  { MonoidHom.id α, OrderHom.id with }
#align order_monoid_hom.id OrderMonoidHom.id
#align order_add_monoid_hom.id OrderAddMonoidHom.id

@[to_additive (attr := simp)]
theorem coe_id : ⇑(OrderMonoidHom.id α) = id :=
  rfl
#align order_monoid_hom.coe_id OrderMonoidHom.coe_id
#align order_add_monoid_hom.coe_id OrderAddMonoidHom.coe_id

@[to_additive]
instance : Inhabited (α →*o α) :=
  ⟨OrderMonoidHom.id α⟩

variable {α}

/-- Composition of `OrderMonoidHom`s as an `OrderMonoidHom`. -/
@[to_additive "Composition of `OrderAddMonoidHom`s as an `OrderAddMonoidHom`"]
def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
  { f.toMonoidHom.comp (g : α →* β), f.toOrderHom.comp (g : α →o β) with }
#align order_monoid_hom.comp OrderMonoidHom.comp
#align order_add_monoid_hom.comp OrderAddMonoidHom.comp

@[to_additive (attr := simp)]
theorem coe_comp (f : β →*o γ) (g : α →*o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align order_monoid_hom.coe_comp OrderMonoidHom.coe_comp
#align order_add_monoid_hom.coe_comp OrderAddMonoidHom.coe_comp

@[to_additive (attr := simp)]
theorem comp_apply (f : β →*o γ) (g : α →*o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align order_add_monoid_hom.comp_apply OrderAddMonoidHom.comp_apply
#align order_monoid_hom.comp_apply OrderMonoidHom.comp_apply

@[to_additive]
theorem coe_comp_monoidHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →* γ) = (f : β →* γ).comp g :=
  rfl
#align order_monoid_hom.coe_comp_monoid_hom OrderMonoidHom.coe_comp_monoidHom
#align order_add_monoid_hom.coe_comp_add_monoid_hom OrderAddMonoidHom.coe_comp_addMonoidHom

@[to_additive]
theorem coe_comp_orderHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →o γ) = (f : β →o γ).comp g :=
  rfl
#align order_monoid_hom.coe_comp_order_hom OrderMonoidHom.coe_comp_orderHom
#align order_add_monoid_hom.coe_comp_order_hom OrderAddMonoidHom.coe_comp_orderHom

@[to_additive (attr := simp)]
theorem comp_assoc (f : γ →*o δ) (g : β →*o γ) (h : α →*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align order_monoid_hom.comp_assoc OrderMonoidHom.comp_assoc
#align order_add_monoid_hom.comp_assoc OrderAddMonoidHom.comp_assoc

@[to_additive (attr := simp)]
theorem comp_id (f : α →*o β) : f.comp (OrderMonoidHom.id α) = f :=
  rfl
#align order_monoid_hom.comp_id OrderMonoidHom.comp_id
#align order_add_monoid_hom.comp_id OrderAddMonoidHom.comp_id

@[to_additive (attr := simp)]
theorem id_comp (f : α →*o β) : (OrderMonoidHom.id β).comp f = f :=
  rfl
#align order_monoid_hom.id_comp OrderMonoidHom.id_comp
#align order_add_monoid_hom.id_comp OrderAddMonoidHom.id_comp

@[to_additive]
theorem cancel_right {g₁ g₂ : β →*o γ} {f : α →*o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun _ => by congr⟩
                                                                   -- 🎉 no goals
#align order_monoid_hom.cancel_right OrderMonoidHom.cancel_right
#align order_add_monoid_hom.cancel_right OrderAddMonoidHom.cancel_right

@[to_additive]
theorem cancel_left {g : β →*o γ} {f₁ f₂ : α →*o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align order_monoid_hom.cancel_left OrderMonoidHom.cancel_left
#align order_add_monoid_hom.cancel_left OrderAddMonoidHom.cancel_left

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive "`0` is the homomorphism sending all elements to `0`."]
instance : One (α →*o β) :=
  ⟨{ (1 : α →* β) with monotone' := monotone_const }⟩

@[to_additive (attr := simp)]
theorem coe_one : ⇑(1 : α →*o β) = 1 :=
  rfl
#align order_monoid_hom.coe_one OrderMonoidHom.coe_one
#align order_add_monoid_hom.coe_zero OrderAddMonoidHom.coe_zero

@[to_additive (attr := simp)]
theorem one_apply (a : α) : (1 : α →*o β) a = 1 :=
  rfl
#align order_monoid_hom.one_apply OrderMonoidHom.one_apply
#align order_add_monoid_hom.zero_apply OrderAddMonoidHom.zero_apply

@[to_additive (attr := simp)]
theorem one_comp (f : α →*o β) : (1 : β →*o γ).comp f = 1 :=
  rfl
#align order_monoid_hom.one_comp OrderMonoidHom.one_comp
#align order_add_monoid_hom.zero_comp OrderAddMonoidHom.zero_comp

@[to_additive (attr := simp)]
theorem comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 :=
  ext fun _ => map_one f
#align order_monoid_hom.comp_one OrderMonoidHom.comp_one
#align order_add_monoid_hom.comp_zero OrderAddMonoidHom.comp_zero

end Preorder

section Mul

variable [OrderedCommMonoid α] [OrderedCommMonoid β] [OrderedCommMonoid γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
@[to_additive "For two ordered additive monoid morphisms `f` and `g`, their product is the ordered
additive monoid morphism sending `a` to `f a + g a`."]
instance : Mul (α →*o β) :=
  ⟨fun f g => { (f * g : α →* β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[to_additive (attr := simp)]
theorem coe_mul (f g : α →*o β) : ⇑(f * g) = f * g :=
  rfl
#align order_monoid_hom.coe_mul OrderMonoidHom.coe_mul
#align order_add_monoid_hom.coe_add OrderAddMonoidHom.coe_add

@[to_additive (attr := simp)]
theorem mul_apply (f g : α →*o β) (a : α) : (f * g) a = f a * g a :=
  rfl
#align order_monoid_hom.mul_apply OrderMonoidHom.mul_apply
#align order_add_monoid_hom.add_apply OrderAddMonoidHom.add_apply

@[to_additive]
theorem mul_comp (g₁ g₂ : β →*o γ) (f : α →*o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
#align order_monoid_hom.mul_comp OrderMonoidHom.mul_comp
#align order_add_monoid_hom.add_comp OrderAddMonoidHom.add_comp

@[to_additive]
theorem comp_mul (g : β →*o γ) (f₁ f₂ : α →*o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _
#align order_monoid_hom.comp_mul OrderMonoidHom.comp_mul
#align order_add_monoid_hom.comp_add OrderAddMonoidHom.comp_add

end Mul

section OrderedCommMonoid

variable {hα : OrderedCommMonoid α} {hβ : OrderedCommMonoid β}

@[to_additive (attr := simp)]
theorem toMonoidHom_eq_coe (f : α →*o β) : f.toMonoidHom = f :=
  rfl
#align order_monoid_hom.to_monoid_hom_eq_coe OrderMonoidHom.toMonoidHom_eq_coe
#align order_add_monoid_hom.to_add_monoid_hom_eq_coe OrderAddMonoidHom.toAddMonoidHom_eq_coe

@[to_additive (attr := simp)]
theorem toOrderHom_eq_coe (f : α →*o β) : f.toOrderHom = f :=
  rfl
#align order_monoid_hom.to_order_hom_eq_coe OrderMonoidHom.toOrderHom_eq_coe
#align order_add_monoid_hom.to_order_hom_eq_coe OrderAddMonoidHom.toOrderHom_eq_coe

end OrderedCommMonoid

section OrderedCommGroup

variable {hα : OrderedCommGroup α} {hβ : OrderedCommGroup β}

/-- Makes an ordered group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive
      "Makes an ordered additive group homomorphism from a proof that the map preserves
      addition."]
def mk' (f : α → β) (hf : Monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }
#align order_monoid_hom.mk' OrderMonoidHom.mk'
#align order_add_monoid_hom.mk' OrderAddMonoidHom.mk'

end OrderedCommGroup

end OrderMonoidHom

namespace OrderMonoidWithZeroHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

instance : OrderMonoidWithZeroHomClass (α →*₀o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    -- ⊢ { toMonoidWithZeroHom := { toZeroHom := { toFun := toFun✝, map_zero' := map_ …
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    -- ⊢ { toMonoidWithZeroHom := { toZeroHom := { toFun := toFun✝¹, map_zero' := map …
    congr
    -- 🎉 no goals
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  monotone f := f.monotone'

-- Porting note:
-- These helper instances are unhelpful in Lean 4, so omitting:
--/-- Helper instance for when there's too many metavariables to apply `FunLike.instCoeFunForAll`
--directly. -/
--instance : CoeFun (α →*₀o β) fun _ => α → β :=
--  FunLike.instCoeFunForAll

-- Other lemmas should be accessed through the `FunLike` API
@[ext]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align order_monoid_with_zero_hom.ext OrderMonoidWithZeroHom.ext

theorem toFun_eq_coe (f : α →*₀o β) : f.toFun = (f : α → β) :=
  rfl
#align order_monoid_with_zero_hom.to_fun_eq_coe OrderMonoidWithZeroHom.toFun_eq_coe

@[simp]
theorem coe_mk (f : α →*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α → β) = f :=
  rfl
#align order_monoid_with_zero_hom.coe_mk OrderMonoidWithZeroHom.coe_mk

@[simp]
theorem mk_coe (f : α →*₀o β) (h) : OrderMonoidWithZeroHom.mk (f : α →*₀ β) h = f := rfl
#align order_monoid_with_zero_hom.mk_coe OrderMonoidWithZeroHom.mk_coe

/-- Reinterpret an ordered monoid with zero homomorphism as an order monoid homomorphism. -/
def toOrderMonoidHom (f : α →*₀o β) : α →*o β :=
  { f with }
#align order_monoid_with_zero_hom.to_order_monoid_hom OrderMonoidWithZeroHom.toOrderMonoidHom

@[simp]
theorem coe_monoidWithZeroHom (f : α →*₀o β) : ⇑(f : α →*₀ β) = f :=
  rfl
#align order_monoid_with_zero_hom.coe_monoid_with_zero_hom OrderMonoidWithZeroHom.coe_monoidWithZeroHom

@[simp]
theorem coe_orderMonoidHom (f : α →*₀o β) : ⇑(f : α →*o β) = f :=
  rfl
#align order_monoid_with_zero_hom.coe_order_monoid_hom OrderMonoidWithZeroHom.coe_orderMonoidHom

theorem toOrderMonoidHom_injective : Injective (toOrderMonoidHom : _ → α →*o β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h using 0
            -- 🎉 no goals
#align order_monoid_with_zero_hom.to_order_monoid_hom_injective OrderMonoidWithZeroHom.toOrderMonoidHom_injective

theorem toMonoidWithZeroHom_injective : Injective (toMonoidWithZeroHom : _ → α →*₀ β) :=
  fun f g h => ext <| by convert FunLike.ext_iff.1 h using 0
                         -- 🎉 no goals
#align order_monoid_with_zero_hom.to_monoid_with_zero_hom_injective OrderMonoidWithZeroHom.toMonoidWithZeroHom_injective

/-- Copy of an `OrderMonoidWithZeroHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }
#align order_monoid_with_zero_hom.copy OrderMonoidWithZeroHom.copy

@[simp]
theorem coe_copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align order_monoid_with_zero_hom.coe_copy OrderMonoidWithZeroHom.coe_copy

theorem copy_eq (f : α →*₀o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align order_monoid_with_zero_hom.copy_eq OrderMonoidWithZeroHom.copy_eq

variable (α)

/-- The identity map as an ordered monoid with zero homomorphism. -/
protected def id : α →*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }
#align order_monoid_with_zero_hom.id OrderMonoidWithZeroHom.id

@[simp]
theorem coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id :=
  rfl
#align order_monoid_with_zero_hom.coe_id OrderMonoidWithZeroHom.coe_id

instance : Inhabited (α →*₀o α) :=
  ⟨OrderMonoidWithZeroHom.id α⟩

variable {α}

/-- Composition of `OrderMonoidWithZeroHom`s as an `OrderMonoidWithZeroHom`. -/
def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
  { f.toMonoidWithZeroHom.comp (g : α →*₀ β), f.toOrderMonoidHom.comp (g : α →*o β) with }
#align order_monoid_with_zero_hom.comp OrderMonoidWithZeroHom.comp

@[simp]
theorem coe_comp (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align order_monoid_with_zero_hom.coe_comp OrderMonoidWithZeroHom.coe_comp

@[simp]
theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align order_monoid_with_zero_hom.comp_apply OrderMonoidWithZeroHom.comp_apply

theorem coe_comp_monoidWithZeroHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g :=
  rfl
#align order_monoid_with_zero_hom.coe_comp_monoid_with_zero_hom OrderMonoidWithZeroHom.coe_comp_monoidWithZeroHom

theorem coe_comp_orderMonoidHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl
#align order_monoid_with_zero_hom.coe_comp_order_monoid_hom OrderMonoidWithZeroHom.coe_comp_orderMonoidHom

@[simp]
theorem comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align order_monoid_with_zero_hom.comp_assoc OrderMonoidWithZeroHom.comp_assoc

@[simp]
theorem comp_id (f : α →*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f := rfl
#align order_monoid_with_zero_hom.comp_id OrderMonoidWithZeroHom.comp_id

@[simp]
theorem id_comp (f : α →*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f := rfl
#align order_monoid_with_zero_hom.id_comp OrderMonoidWithZeroHom.id_comp

theorem cancel_right {g₁ g₂ : β →*₀o γ} {f : α →*₀o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun _ => by congr⟩
                                                                   -- 🎉 no goals
#align order_monoid_with_zero_hom.cancel_right OrderMonoidWithZeroHom.cancel_right

theorem cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align order_monoid_with_zero_hom.cancel_left OrderMonoidWithZeroHom.cancel_left

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
#align order_monoid_with_zero_hom.coe_mul OrderMonoidWithZeroHom.coe_mul

@[simp]
theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
  rfl
#align order_monoid_with_zero_hom.mul_apply OrderMonoidWithZeroHom.mul_apply

theorem mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
#align order_monoid_with_zero_hom.mul_comp OrderMonoidWithZeroHom.mul_comp

theorem comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _
#align order_monoid_with_zero_hom.comp_mul OrderMonoidWithZeroHom.comp_mul

end Mul

section LinearOrderedCommMonoidWithZero

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}

@[simp]
theorem toMonoidWithZeroHom_eq_coe (f : α →*₀o β) : f.toMonoidWithZeroHom = f := by
  rfl
  -- 🎉 no goals
#align order_monoid_with_zero_hom.to_monoid_with_zero_hom_eq_coe OrderMonoidWithZeroHom.toMonoidWithZeroHom_eq_coe

@[simp]
theorem toOrderMonoidHom_eq_coe (f : α →*₀o β) : f.toOrderMonoidHom = f :=
  rfl
#align order_monoid_with_zero_hom.to_order_monoid_hom_eq_coe OrderMonoidWithZeroHom.toOrderMonoidHom_eq_coe

end LinearOrderedCommMonoidWithZero

end OrderMonoidWithZeroHom
