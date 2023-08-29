/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Equiv

#align_import algebra.order.hom.ring from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `OrderRingHom` : Monotone semiring homomorphisms.
* `OrderRingIso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Tags

ordered ring homomorphism, order homomorphism
-/


open Function

variable {F α β γ δ : Type*}

/-- `OrderRingHom α β` is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : OrderRingHom α β)`,
you should parametrize over `(F : Type*) [OrderRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingHomClass`. -/
structure OrderRingHom (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α →+* β where
  /-- The proposition that the function preserves the order. -/
  monotone' : Monotone toFun
#align order_ring_hom OrderRingHom

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

@[inherit_doc]
infixl:25 " →+*o " => OrderRingHom

/- Porting note: Needed to reorder instance arguments below:
`[Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]`
to
`[Mul α] [Mul β] [Add α] [Add β] [LE α] [LE β]`
otherwise the [refl] attribute on `OrderRingIso.refl` complains.
TODO: change back when `refl` attribute is fixed, github issue #2505 -/

/-- `OrderRingHom α β` is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : OrderRingIso α β)`,
you should parametrize over `(F : Type*) [OrderRingIsoClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingIsoClass`. -/
structure OrderRingIso (α β : Type*) [Mul α] [Mul β] [Add α] [Add β] [LE α] [LE β] extends
  α ≃+* β where
  /-- The proposition that the function preserves the order bijectively. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b
#align order_ring_iso OrderRingIso

@[inherit_doc]
infixl:25 " ≃+*o " => OrderRingIso

/-- `OrderRingHomClass F α β` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `OrderRingHom`. -/
class OrderRingHomClass (F : Type*) (α β : outParam <| Type*) [NonAssocSemiring α] [Preorder α]
  [NonAssocSemiring β] [Preorder β] extends RingHomClass F α β where
  /-- The proposition that the function preserves the order. -/
  monotone (f : F) : Monotone f
#align order_ring_hom_class OrderRingHomClass

/-- `OrderRingIsoClass F α β` states that `F` is a type of ordered semiring isomorphisms.
You should extend this class when you extend `OrderRingIso`. -/
class OrderRingIsoClass (F : Type*) (α β : outParam (Type*)) [Mul α] [Add α] [LE α] [Mul β]
  [Add β] [LE β] extends RingEquivClass F α β where
  /-- The proposition that the function preserves the order bijectively. -/
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
#align order_ring_hom_class.to_order_monoid_with_zero_hom_class OrderRingHomClass.toOrderMonoidWithZeroHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderRingIsoClass.toOrderIsoClass [Mul α] [Add α] [LE α]
  [Mul β] [Add β] [LE β] [OrderRingIsoClass F α β] : OrderIsoClass F α β :=
  { ‹OrderRingIsoClass F α β› with }
#align order_ring_iso_class.to_order_iso_class OrderRingIsoClass.toOrderIsoClass

-- See note [lower instance priority]
instance (priority := 100) OrderRingIsoClass.toOrderRingHomClass [NonAssocSemiring α]
  [Preorder α] [NonAssocSemiring β] [Preorder β] [OrderRingIsoClass F α β] :
    OrderRingHomClass F α β :=
  { monotone := fun f _ _ => (map_le_map_iff f).2
    -- porting note: used to be the following which times out
    --‹OrderRingIsoClass F α β› with monotone := fun f => OrderHomClass.mono f
    }
#align order_ring_iso_class.to_order_ring_hom_class OrderRingIsoClass.toOrderRingHomClass

-- porting note: OrderRingHomClass.toOrderRingHom is new
/-- Turn an element of a type `F` satisfying `OrderRingHomClass F α β` into an actual
`OrderRingHom`. This is declared as the default coercion from `F` to `α →+*o β`. -/
@[coe]
def OrderRingHomClass.toOrderRingHom [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
    [Preorder β] [OrderRingHomClass F α β] (f : F) : α →+*o β :=
{ (f : α →+* β) with monotone' := monotone f}

/-- Any type satisfying `OrderRingHomClass` can be cast into `OrderRingHom` via
  `OrderRingHomClass.toOrderRingHom`. -/
instance [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]
    [OrderRingHomClass F α β] : CoeTC F (α →+*o β) :=
  ⟨OrderRingHomClass.toOrderRingHom⟩

-- porting note: OrderRingIsoClass.toOrderRingIso is new
/-- Turn an element of a type `F` satisfying `OrderRingIsoClass F α β` into an actual
`OrderRingIso`. This is declared as the default coercion from `F` to `α ≃+*o β`. -/
@[coe]
def OrderRingIsoClass.toOrderRingIso [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
    [OrderRingIsoClass F α β] (f : F) : α ≃+*o β :=
{ (f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f}

/-- Any type satisfying `OrderRingIsoClass` can be cast into `OrderRingIso` via
  `OrderRingIsoClass.toOrderRingIso`. -/
instance [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderRingIsoClass F α β] :
    CoeTC F (α ≃+*o β) :=
  ⟨OrderRingIsoClass.toOrderRingIso⟩

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
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
    -- ⊢ { toRingHom := { toMonoidHom := toMonoidHom✝, map_zero' := map_zero'✝, map_a …
                             -- ⊢ { toRingHom := { toMonoidHom := toMonoidHom✝¹, map_zero' := map_zero'✝¹, map …
                                                      -- ⊢ toMonoidHom✝¹ = toMonoidHom✝
    -- porting note: needed to add the following line
    exact MonoidHom.monoidHomClass.coe_injective' h
    -- 🎉 no goals
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  monotone f := f.monotone'

-- porting note: These helper instances are unhelpful in Lean 4, so omitting:
-- /-- Helper instance for when there's too many metavariables to apply `FunLike.has_coe_to_fun`
-- directly. -/
-- instance : CoeFun (α →+*o β) fun _ => α → β :=
--   ⟨fun f => f.toFun⟩

theorem toFun_eq_coe (f : α →+*o β) : f.toFun = f :=
  rfl
#align order_ring_hom.to_fun_eq_coe OrderRingHom.toFun_eq_coe

@[ext]
theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align order_ring_hom.ext OrderRingHom.ext

@[simp]
theorem toRingHom_eq_coe (f : α →+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl
#align order_ring_hom.to_ring_hom_eq_coe OrderRingHom.toRingHom_eq_coe

@[simp]
theorem toOrderAddMonoidHom_eq_coe (f : α →+*o β) : f.toOrderAddMonoidHom = f :=
  rfl
#align order_ring_hom.to_order_add_monoid_hom_eq_coe OrderRingHom.toOrderAddMonoidHom_eq_coe

@[simp]
theorem toOrderMonoidWithZeroHom_eq_coe (f : α →+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl
#align order_ring_hom.to_order_monoid_with_zero_hom_eq_coe OrderRingHom.toOrderMonoidWithZeroHom

@[simp]
theorem coe_coe_ringHom (f : α →+*o β) : ⇑(f : α →+* β) = f :=
  rfl
#align order_ring_hom.coe_coe_ring_hom OrderRingHom.coe_coe_ringHom

@[simp]
theorem coe_coe_orderAddMonoidHom (f : α →+*o β) : ⇑(f : α →+o β) = f :=
  rfl
#align order_ring_hom.coe_coe_order_add_monoid_hom OrderRingHom.coe_coe_orderAddMonoidHom

@[simp]
theorem coe_coe_orderMonoidWithZeroHom (f : α →+*o β) : ⇑(f : α →*₀o β) = f :=
  rfl
#align order_ring_hom.coe_coe_order_monoid_with_zero_hom OrderRingHom.coe_coe_orderMonoidWithZeroHom

@[norm_cast]
theorem coe_ringHom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a :=
  rfl
#align order_ring_hom.coe_ring_hom_apply OrderRingHom.coe_ringHom_apply

@[norm_cast]
theorem coe_orderAddMonoidHom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
  rfl
#align order_ring_hom.coe_order_add_monoid_hom_apply OrderRingHom.coe_orderAddMonoidHom_apply

@[norm_cast]
theorem coe_orderMonoidWithZeroHom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a :=
  rfl
#align order_ring_hom.coe_order_monoid_with_zero_hom_apply OrderRingHom.coe_orderMonoidWithZeroHom_apply

/-- Copy of an `OrderRingHom` with a new `toFun` equal to the old one. Useful to fix definitional
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
theorem coe_ringHom_id : (OrderRingHom.id α : α →+* α) = RingHom.id α :=
  rfl
#align order_ring_hom.coe_ring_hom_id OrderRingHom.coe_ringHom_id

@[simp]
theorem coe_orderAddMonoidHom_id : (OrderRingHom.id α : α →+o α) = OrderAddMonoidHom.id α :=
  rfl
#align order_ring_hom.coe_order_add_monoid_hom_id OrderRingHom.coe_orderAddMonoidHom_id

@[simp]
theorem coe_orderMonoidWithZeroHom_id :
    (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl
#align order_ring_hom.coe_order_monoid_with_zero_hom_id OrderRingHom.coe_orderMonoidWithZeroHom_id

/-- Composition of two `OrderRingHom`s as an `OrderRingHom`. -/
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
  rfl
#align order_ring_hom.comp_id OrderRingHom.comp_id

@[simp]
theorem id_comp (f : α →+*o β) : (OrderRingHom.id β).comp f = f :=
  rfl
#align order_ring_hom.id_comp OrderRingHom.id_comp

theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, fun h => by rw [h]⟩
                                                                   -- 🎉 no goals
#align order_ring_hom.cancel_right OrderRingHom.cancel_right
theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align order_ring_hom.cancel_left OrderRingHom.cancel_left

end Preorder

variable [NonAssocSemiring β]

instance [Preorder β] : Preorder (OrderRingHom α β) :=
  Preorder.lift ((⇑) : _ → α → β)

instance [PartialOrder β] : PartialOrder (OrderRingHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

end OrderRingHom

/-! ### Ordered ring isomorphisms -/


namespace OrderRingIso

section LE

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ] [Mul δ] [Add δ] [LE δ]

/-- Reinterpret an ordered ring isomorphism as an order isomorphism. -/
-- Porting note: Added @[coe] attribute
@[coe]
def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩
#align order_ring_iso.to_order_iso OrderRingIso.toOrderIso

instance : OrderRingIsoClass (α ≃+*o β) α β
    where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    -- ⊢ { toRingEquiv := { toEquiv := { toFun := toFun✝, invFun := invFun✝, left_inv …
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    -- ⊢ { toRingEquiv := { toEquiv := { toFun := toFun✝¹, invFun := invFun✝¹, left_i …
    congr
    -- 🎉 no goals
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  map_le_map_iff f _ _ := f.map_le_map_iff'
  left_inv f := f.left_inv
  right_inv f := f.right_inv

-- porting note: These helper instances are unhelpful in Lean 4, so omitting:
/-- Helper instance for when there's too many metavariables to apply `FunLike.has_coe_to_fun`
directly. -/
-- instance : CoeFun (α ≃+*o β) fun _ => α → β :=
--   FunLike.has_coe_to_fun

theorem toFun_eq_coe (f : α ≃+*o β) : f.toFun = f :=
  rfl
#align order_ring_iso.to_fun_eq_coe OrderRingIso.toFun_eq_coe

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
theorem toRingEquiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f :=
  RingEquiv.ext fun _ => rfl
#align order_ring_iso.to_ring_equiv_eq_coe OrderRingIso.toRingEquiv_eq_coe

@[simp]
theorem toOrderIso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f :=
  OrderIso.ext rfl
#align order_ring_iso.to_order_iso_eq_coe OrderRingIso.toOrderIso_eq_coe

@[simp, norm_cast]
theorem coe_toRingEquiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f :=
  rfl
#align order_ring_iso.coe_to_ring_equiv OrderRingIso.coe_toRingEquiv

-- Porting note: needed to add FunLike.coe on the lhs, bad Equiv coercion otherwise
@[simp, norm_cast]
theorem coe_toOrderIso (f : α ≃+*o β) : FunLike.coe (f : α ≃o β) = f :=
  rfl
#align order_ring_iso.coe_to_order_iso OrderRingIso.coe_toOrderIso

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl]
protected def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, Iff.rfl⟩
#align order_ring_iso.refl OrderRingIso.refl

instance : Inhabited (α ≃+*o α) :=
  ⟨OrderRingIso.refl α⟩

@[simp]
theorem refl_apply (x : α) : OrderRingIso.refl α x = x := by
  rfl
  -- 🎉 no goals
#align order_ring_iso.refl_apply OrderRingIso.refl_apply

@[simp]
theorem coe_ringEquiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α :=
  rfl
#align order_ring_iso.coe_ring_equiv_refl OrderRingIso.coe_ringEquiv_refl

@[simp]
theorem coe_orderIso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
  rfl
#align order_ring_iso.coe_order_iso_refl OrderRingIso.coe_orderIso_refl

variable {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm]
protected def symm (e : α ≃+*o β) : β ≃+*o α :=
  ⟨e.toRingEquiv.symm, by
    intro a b
    -- ⊢ Equiv.toFun (RingEquiv.symm e.toRingEquiv).toEquiv a ≤ Equiv.toFun (RingEqui …
    erw [← map_le_map_iff e, e.1.apply_symm_apply, e.1.apply_symm_apply]⟩
    -- 🎉 no goals
#align order_ring_iso.symm OrderRingIso.symm

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : α ≃+*o β) : β → α :=
  e.symm
#align order_ring_iso.simps.symm_apply OrderRingIso.Simps.symm_apply

@[simp]
theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e :=
  ext fun _ => rfl
#align order_ring_iso.symm_symm OrderRingIso.symm_symm

/-- Composition of `OrderRingIso`s as an `OrderRingIso`. -/
@[trans]
protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩
#align order_ring_iso.trans OrderRingIso.trans

/- Porting note: Used to be generated by [simps] on `trans`, but the lhs of this simplifies under
simp, so problem with the simpNF linter. Removed [simps] attribute and added aux version below. -/
theorem trans_toRingEquiv (f : α ≃+*o β) (g : β ≃+*o γ) :
    (OrderRingIso.trans f g).toRingEquiv = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

@[simp]
theorem trans_toRingEquiv_aux (f : α ≃+*o β) (g : β ≃+*o γ) :
    RingEquivClass.toRingEquiv (OrderRingIso.trans f g)
      = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

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
  ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩
#align order_ring_iso.to_order_ring_hom OrderRingIso.toOrderRingHom

@[simp]
theorem toOrderRingHom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f :=
  rfl
#align order_ring_iso.to_order_ring_hom_eq_coe OrderRingIso.toOrderRingHom_eq_coe

@[simp, norm_cast]
theorem coe_toOrderRingHom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f :=
  rfl
#align order_ring_iso.coe_to_order_ring_hom OrderRingIso.coe_toOrderRingHom

@[simp]
theorem coe_toOrderRingHom_refl : (OrderRingIso.refl α : α →+*o α) = OrderRingHom.id α :=
  rfl
#align order_ring_iso.coe_to_order_ring_hom_refl OrderRingIso.coe_toOrderRingHom_refl

theorem toOrderRingHom_injective : Injective (toOrderRingHom : α ≃+*o β → α →+*o β) :=
  fun f g h => FunLike.coe_injective <| by convert FunLike.ext'_iff.1 h using 0
                                           -- 🎉 no goals
#align order_ring_iso.to_order_ring_hom_injective OrderRingIso.toOrderRingHom_injective

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
    -- ⊢ ↑f x = ↑g x
    by_contra' h' : f x ≠ g x
    -- ⊢ False
    wlog h : f x < g x generalizing α β with h₂
    -- ⊢ False
    -- porting note: had to add the `generalizing` as there are random variables
    -- `F γ δ` flying around in context.
    · exact h₂ g f x (Ne.symm h') (h'.lt_or_lt.resolve_left h)
      -- 🎉 no goals
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    -- ⊢ False
    rw [← map_ratCast f] at hf
    -- ⊢ False
    rw [← map_ratCast g] at hg
    -- ⊢ False
    exact
      (lt_asymm ((OrderHomClass.mono g).reflect_lt hg) <|
          (OrderHomClass.mono f).reflect_lt hf).elim⟩
#align order_ring_hom.subsingleton OrderRingHom.subsingleton

/-- There is at most one ordered ring isomorphism between a linear ordered field and an archimedean
linear ordered field. -/
instance OrderRingIso.subsingleton_right [LinearOrderedField α] [LinearOrderedField β]
    [Archimedean β] : Subsingleton (α ≃+*o β) :=
  OrderRingIso.toOrderRingHom_injective.subsingleton
#align order_ring_iso.subsingleton_right OrderRingIso.subsingleton_right

/-- There is at most one ordered ring isomorphism between an archimedean linear ordered field and a
linear ordered field. -/
instance OrderRingIso.subsingleton_left [LinearOrderedField α] [Archimedean α]
    [LinearOrderedField β] : Subsingleton (α ≃+*o β) :=
  OrderRingIso.symm_bijective.injective.subsingleton
#align order_ring_iso.subsingleton_left OrderRingIso.subsingleton_left
