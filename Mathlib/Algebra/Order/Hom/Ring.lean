/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.hom.ring
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Order.Hom.Monoid
import Mathbin.Algebra.Order.Ring.Defs
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Tactic.ByContra
import Mathbin.Tactic.Wlog

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `order_ring_hom` : Monotone semiring homomorphisms.
* `order_ring_iso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Tags

ordered ring homomorphism, order homomorphism
-/


open Function

variable {F α β γ δ : Type _}

/-- `order_ring_hom α β` is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : order_ring_hom α β)`,
you should parametrize over `(F : Type*) [order_ring_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_ring_hom_class`. -/
structure OrderRingHom (α β : Type _) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α →+* β where
  monotone' : Monotone to_fun
#align order_ring_hom OrderRingHom

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

-- mathport name: «expr →+*o »
infixl:25 " →+*o " => OrderRingHom

/-- `order_ring_hom α β` is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : order_ring_iso α β)`,
you should parametrize over `(F : Type*) [order_ring_iso_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_ring_iso_class`. -/
structure OrderRingIso (α β : Type _) [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] extends
  α ≃+* β where
  map_le_map_iff' {a b : α} : to_fun a ≤ to_fun b ↔ a ≤ b
#align order_ring_iso OrderRingIso

-- mathport name: «expr ≃+*o »
infixl:25 " ≃+*o " => OrderRingIso

/-- `order_ring_hom_class F α β` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `order_ring_hom`. -/
class OrderRingHomClass (F : Type _) (α β : outParam <| Type _) [NonAssocSemiring α] [Preorder α]
  [NonAssocSemiring β] [Preorder β] extends RingHomClass F α β where
  Monotone (f : F) : Monotone f
#align order_ring_hom_class OrderRingHomClass

/-- `order_ring_iso_class F α β` states that `F` is a type of ordered semiring isomorphisms.
You should extend this class when you extend `order_ring_iso`. -/
class OrderRingIsoClass (F : Type _) (α β : outParam (Type _)) [Mul α] [Add α] [LE α] [Mul β]
  [Add β] [LE β] extends RingEquivClass F α β where
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b
#align order_ring_iso_class OrderRingIsoClass

-- See note [lower priority instance]
instance (priority := 100) OrderRingHomClass.toOrderAddMonoidHomClass [NonAssocSemiring α]
    [Preorder α] [NonAssocSemiring β] [Preorder β] [OrderRingHomClass F α β] :
    OrderAddMonoidHomClass F α β :=
  { ‹OrderRingHomClass F α β› with }
#align order_ring_hom_class.to_order_add_monoid_hom_class OrderRingHomClass.toOrderAddMonoidHomClass

-- See note [lower priority instance]
instance (priority := 100) OrderRingHomClass.toOrderMonoidWithZeroHomClass [NonAssocSemiring α]
    [Preorder α] [NonAssocSemiring β] [Preorder β] [OrderRingHomClass F α β] :
    OrderMonoidWithZeroHomClass F α β :=
  { ‹OrderRingHomClass F α β› with }
#align
  order_ring_hom_class.to_order_monoid_with_zero_hom_class OrderRingHomClass.toOrderMonoidWithZeroHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderRingIsoClass.toOrderIsoClass [Mul α] [Add α] [LE α] [Mul β] [Add β]
    [LE β] [OrderRingIsoClass F α β] : OrderIsoClass F α β :=
  { ‹OrderRingIsoClass F α β› with }
#align order_ring_iso_class.to_order_iso_class OrderRingIsoClass.toOrderIsoClass

-- See note [lower instance priority]
instance (priority := 100) OrderRingIsoClass.toOrderRingHomClass [NonAssocSemiring α] [Preorder α]
    [NonAssocSemiring β] [Preorder β] [OrderRingIsoClass F α β] : OrderRingHomClass F α β :=
  { ‹OrderRingIsoClass F α β› with Monotone := fun f => OrderHomClass.mono f }
#align order_ring_iso_class.to_order_ring_hom_class OrderRingIsoClass.toOrderRingHomClass

instance [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]
    [OrderRingHomClass F α β] : CoeTC F (α →+*o β) :=
  ⟨fun f => ⟨f, OrderHomClass.mono f⟩⟩

instance [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderRingIsoClass F α β] :
    CoeTC F (α ≃+*o β) :=
  ⟨fun f => ⟨f, fun a b => map_le_map_iff f⟩⟩

/-! ### Ordered ring homomorphisms -/


namespace OrderRingHom

variable [NonAssocSemiring α] [Preorder α]

section Preorder

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

/-- Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorphism. -/
def toOrderAddMonoidHom (f : α →+*o β) : α →+o β :=
  { f with }
#align order_ring_hom.to_order_add_monoid_hom OrderRingHom.toOrderAddMonoidHom

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def toOrderMonoidWithZeroHom (f : α →+*o β) : α →*₀o β :=
  { f with }
#align order_ring_hom.to_order_monoid_with_zero_hom OrderRingHom.toOrderMonoidWithZeroHom

instance : OrderRingHomClass (α →+*o β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  Monotone f := f.monotone'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →+*o β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

theorem to_fun_eq_coe (f : α →+*o β) : f.toFun = ⇑f :=
  rfl
#align order_ring_hom.to_fun_eq_coe OrderRingHom.to_fun_eq_coe

@[ext]
theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align order_ring_hom.ext OrderRingHom.ext

@[simp]
theorem to_ring_hom_eq_coe (f : α →+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl
#align order_ring_hom.to_ring_hom_eq_coe OrderRingHom.to_ring_hom_eq_coe

@[simp]
theorem to_order_add_monoid_hom_eq_coe (f : α →+*o β) : f.toOrderAddMonoidHom = f :=
  rfl
#align order_ring_hom.to_order_add_monoid_hom_eq_coe OrderRingHom.to_order_add_monoid_hom_eq_coe

@[simp]
theorem to_order_monoid_with_zero_hom_eq_coe (f : α →+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl
#align
  order_ring_hom.to_order_monoid_with_zero_hom_eq_coe OrderRingHom.to_order_monoid_with_zero_hom_eq_coe

@[simp]
theorem coe_coe_ring_hom (f : α →+*o β) : ⇑(f : α →+* β) = f :=
  rfl
#align order_ring_hom.coe_coe_ring_hom OrderRingHom.coe_coe_ring_hom

@[simp]
theorem coe_coe_order_add_monoid_hom (f : α →+*o β) : ⇑(f : α →+o β) = f :=
  rfl
#align order_ring_hom.coe_coe_order_add_monoid_hom OrderRingHom.coe_coe_order_add_monoid_hom

@[simp]
theorem coe_coe_order_monoid_with_zero_hom (f : α →+*o β) : ⇑(f : α →*₀o β) = f :=
  rfl
#align
  order_ring_hom.coe_coe_order_monoid_with_zero_hom OrderRingHom.coe_coe_order_monoid_with_zero_hom

@[norm_cast]
theorem coe_ring_hom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a :=
  rfl
#align order_ring_hom.coe_ring_hom_apply OrderRingHom.coe_ring_hom_apply

@[norm_cast]
theorem coe_order_add_monoid_hom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
  rfl
#align order_ring_hom.coe_order_add_monoid_hom_apply OrderRingHom.coe_order_add_monoid_hom_apply

@[norm_cast]
theorem coe_order_monoid_with_zero_hom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a :=
  rfl
#align
  order_ring_hom.coe_order_monoid_with_zero_hom_apply OrderRingHom.coe_order_monoid_with_zero_hom_apply

/-- Copy of a `order_ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }
#align order_ring_hom.copy OrderRingHom.copy

@[simp]
theorem coe_copy (f : α →+*o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align order_ring_hom.coe_copy OrderRingHom.coe_copy

theorem copy_eq (f : α →+*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align order_ring_hom.copy_eq OrderRingHom.copy_eq

variable (α)

/-- The identity as an ordered ring homomorphism. -/
protected def id : α →+*o α :=
  { RingHom.id _, OrderHom.id with }
#align order_ring_hom.id OrderRingHom.id

instance : Inhabited (α →+*o α) :=
  ⟨OrderRingHom.id α⟩

@[simp]
theorem coe_id : ⇑(OrderRingHom.id α) = id :=
  rfl
#align order_ring_hom.coe_id OrderRingHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : OrderRingHom.id α a = a :=
  rfl
#align order_ring_hom.id_apply OrderRingHom.id_apply

@[simp]
theorem coe_ring_hom_id : (OrderRingHom.id α : α →+* α) = RingHom.id α :=
  rfl
#align order_ring_hom.coe_ring_hom_id OrderRingHom.coe_ring_hom_id

@[simp]
theorem coe_order_add_monoid_hom_id : (OrderRingHom.id α : α →+o α) = OrderAddMonoidHom.id α :=
  rfl
#align order_ring_hom.coe_order_add_monoid_hom_id OrderRingHom.coe_order_add_monoid_hom_id

@[simp]
theorem coe_order_monoid_with_zero_hom_id :
    (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl
#align
  order_ring_hom.coe_order_monoid_with_zero_hom_id OrderRingHom.coe_order_monoid_with_zero_hom_id

/-- Composition of two `order_ring_hom`s as an `order_ring_hom`. -/
protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }
#align order_ring_hom.comp OrderRingHom.comp

@[simp]
theorem coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align order_ring_hom.coe_comp OrderRingHom.coe_comp

@[simp]
theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) :=
  rfl
#align order_ring_hom.comp_apply OrderRingHom.comp_apply

theorem comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align order_ring_hom.comp_assoc OrderRingHom.comp_assoc

@[simp]
theorem comp_id (f : α →+*o β) : f.comp (OrderRingHom.id α) = f :=
  ext fun x => rfl
#align order_ring_hom.comp_id OrderRingHom.comp_id

@[simp]
theorem id_comp (f : α →+*o β) : (OrderRingHom.id β).comp f = f :=
  ext fun x => rfl
#align order_ring_hom.id_comp OrderRingHom.id_comp

theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align order_ring_hom.cancel_right OrderRingHom.cancel_right

theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align order_ring_hom.cancel_left OrderRingHom.cancel_left

end Preorder

variable [NonAssocSemiring β]

instance [Preorder β] : Preorder (OrderRingHom α β) :=
  Preorder.lift (coeFn : _ → α → β)

instance [PartialOrder β] : PartialOrder (OrderRingHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

end OrderRingHom

/-! ### Ordered ring isomorphisms -/


namespace OrderRingIso

section LE

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ] [Mul δ] [Add δ] [LE δ]

/-- Reinterpret an ordered ring isomorphism as an order isomorphism. -/
def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, fun _ _ => f.map_le_map_iff'⟩
#align order_ring_iso.to_order_iso OrderRingIso.toOrderIso

instance : OrderRingIsoClass (α ≃+*o β) α β
    where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  map_le_map_iff f _ _ := f.map_le_map_iff'
  left_inv f := f.left_inv
  right_inv f := f.right_inv

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α ≃+*o β) fun _ => α → β :=
  FunLike.hasCoeToFun

theorem to_fun_eq_coe (f : α ≃+*o β) : f.toFun = f :=
  rfl
#align order_ring_iso.to_fun_eq_coe OrderRingIso.to_fun_eq_coe

@[ext]
theorem ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align order_ring_iso.ext OrderRingIso.ext

@[simp]
theorem coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e :=
  rfl
#align order_ring_iso.coe_mk OrderRingIso.coe_mk

@[simp]
theorem mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e :=
  ext fun _ => rfl
#align order_ring_iso.mk_coe OrderRingIso.mk_coe

@[simp]
theorem to_ring_equiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f :=
  RingEquiv.ext fun _ => rfl
#align order_ring_iso.to_ring_equiv_eq_coe OrderRingIso.to_ring_equiv_eq_coe

@[simp]
theorem to_order_iso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f :=
  OrderIso.ext rfl
#align order_ring_iso.to_order_iso_eq_coe OrderRingIso.to_order_iso_eq_coe

@[simp, norm_cast]
theorem coe_to_ring_equiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f :=
  rfl
#align order_ring_iso.coe_to_ring_equiv OrderRingIso.coe_to_ring_equiv

@[simp, norm_cast]
theorem coe_to_order_iso (f : α ≃+*o β) : ⇑(f : α ≃o β) = f :=
  rfl
#align order_ring_iso.coe_to_order_iso OrderRingIso.coe_to_order_iso

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl]
protected def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, fun _ _ => Iff.rfl⟩
#align order_ring_iso.refl OrderRingIso.refl

instance : Inhabited (α ≃+*o α) :=
  ⟨OrderRingIso.refl α⟩

@[simp]
theorem refl_apply (x : α) : OrderRingIso.refl α x = x :=
  rfl
#align order_ring_iso.refl_apply OrderRingIso.refl_apply

@[simp]
theorem coe_ring_equiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α :=
  rfl
#align order_ring_iso.coe_ring_equiv_refl OrderRingIso.coe_ring_equiv_refl

@[simp]
theorem coe_order_iso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
  rfl
#align order_ring_iso.coe_order_iso_refl OrderRingIso.coe_order_iso_refl

variable {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm]
protected def symm (e : α ≃+*o β) : β ≃+*o α :=
  ⟨e.toRingEquiv.symm, fun a b => by
    erw [← map_le_map_iff e, e.1.apply_symm_apply, e.1.apply_symm_apply]⟩
#align order_ring_iso.symm OrderRingIso.symm

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : α ≃+*o β) : β → α :=
  e.symm
#align order_ring_iso.simps.symm_apply OrderRingIso.Simps.symmApply

@[simp]
theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e :=
  ext fun _ => rfl
#align order_ring_iso.symm_symm OrderRingIso.symm_symm

/-- Composition of `order_ring_iso`s as an `order_ring_iso`. -/
@[trans, simps]
protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, fun a b => (map_le_map_iff g).trans (map_le_map_iff f)⟩
#align order_ring_iso.trans OrderRingIso.trans

@[simp]
theorem trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) :=
  rfl
#align order_ring_iso.trans_apply OrderRingIso.trans_apply

@[simp]
theorem self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α :=
  ext e.left_inv
#align order_ring_iso.self_trans_symm OrderRingIso.self_trans_symm

@[simp]
theorem symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β :=
  ext e.right_inv
#align order_ring_iso.symm_trans_self OrderRingIso.symm_trans_self

theorem symm_bijective : Bijective (OrderRingIso.symm : α ≃+*o β → β ≃+*o α) :=
  ⟨fun f g h => f.symm_symm.symm.trans <| (congr_arg OrderRingIso.symm h).trans g.symm_symm,
    fun f => ⟨f.symm, f.symm_symm⟩⟩
#align order_ring_iso.symm_bijective OrderRingIso.symm_bijective

end LE

section NonAssocSemiring

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ]
  [Preorder γ]

/-- Reinterpret an ordered ring isomorphism as an ordered ring homomorphism. -/
def toOrderRingHom (f : α ≃+*o β) : α →+*o β :=
  ⟨f.toRingEquiv.toRingHom, fun a b => (map_le_map_iff f).2⟩
#align order_ring_iso.to_order_ring_hom OrderRingIso.toOrderRingHom

@[simp]
theorem to_order_ring_hom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f :=
  rfl
#align order_ring_iso.to_order_ring_hom_eq_coe OrderRingIso.to_order_ring_hom_eq_coe

@[simp, norm_cast]
theorem coe_to_order_ring_hom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f :=
  rfl
#align order_ring_iso.coe_to_order_ring_hom OrderRingIso.coe_to_order_ring_hom

@[simp]
theorem coe_to_order_ring_hom_refl : (OrderRingIso.refl α : α →+*o α) = OrderRingHom.id α :=
  rfl
#align order_ring_iso.coe_to_order_ring_hom_refl OrderRingIso.coe_to_order_ring_hom_refl

theorem to_order_ring_hom_injective : Injective (toOrderRingHom : α ≃+*o β → α →+*o β) :=
  fun f g h => FunLike.coe_injective <| by convert FunLike.ext'_iff.1 h
#align order_ring_iso.to_order_ring_hom_injective OrderRingIso.to_order_ring_hom_injective

end NonAssocSemiring

end OrderRingIso

/-!
### Uniqueness

There is at most one ordered ring homomorphism from a linear ordered field to an archimedean linear
ordered field. Reciprocally, such an ordered ring homomorphism exists when the codomain is further
conditionally complete.
-/


/-- There is at most one ordered ring homomorphism from a linear ordered field to an archimedean
linear ordered field. -/
instance OrderRingHom.subsingleton [LinearOrderedField α] [LinearOrderedField β] [Archimedean β] :
    Subsingleton (α →+*o β) :=
  ⟨fun f g => by
    ext x
    by_contra' h
    wlog h : f x < g x using f g, g f
    · exact Ne.lt_or_lt h
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_ratCast f] at hf
    rw [← map_ratCast g] at hg
    exact
      (lt_asymm ((OrderHomClass.mono g).reflect_lt hg) <|
          (OrderHomClass.mono f).reflect_lt hf).elim⟩
#align order_ring_hom.subsingleton OrderRingHom.subsingleton

/-- There is at most one ordered ring isomorphism between a linear ordered field and an archimedean
linear ordered field. -/
instance OrderRingIso.subsingleton_right [LinearOrderedField α] [LinearOrderedField β]
    [Archimedean β] : Subsingleton (α ≃+*o β) :=
  OrderRingIso.to_order_ring_hom_injective.Subsingleton
#align order_ring_iso.subsingleton_right OrderRingIso.subsingleton_right

/-- There is at most one ordered ring isomorphism between an archimedean linear ordered field and a
linear ordered field. -/
instance OrderRingIso.subsingleton_left [LinearOrderedField α] [Archimedean α]
    [LinearOrderedField β] : Subsingleton (α ≃+*o β) :=
  OrderRingIso.symm_bijective.Injective.Subsingleton
#align order_ring_iso.subsingleton_left OrderRingIso.subsingleton_left

