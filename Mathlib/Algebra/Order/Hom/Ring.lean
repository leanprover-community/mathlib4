/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Ring.Equiv

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `OrderRingHom` : Monotone semiring homomorphisms.
* `OrderRingIso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Implementation notes

This file used to define typeclasses for order-preserving ring homomorphisms and isomorphisms.
In https://github.com/leanprover-community/mathlib4/pull/10544, we migrated from assumptions like `[FunLike F R S] [OrderRingHomClass F R S]`
to assumptions like `[FunLike F R S] [OrderHomClass F R S] [RingHomClass F R S]`,
making some typeclasses and instances irrelevant.

## Tags

ordered ring homomorphism, order homomorphism
-/

@[expose] public section

assert_not_exists FloorRing Archimedean

open Function

variable {F α β γ δ : Type*}

/-- `OrderRingHom α β`, denoted `α →+*o β`,
is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : OrderRingHom α β)`,
you should parametrize over `(F : Type*) [OrderRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingHomClass`. -/
structure OrderRingHom (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α →+* β where
  /-- The proposition that the function preserves the order. -/
  monotone' : Monotone toFun

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

@[inherit_doc]
infixl:25 " →+*o " => OrderRingHom

/-- `OrderRingIso α β`, denoted as `α ≃+*o β`,
is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : OrderRingIso α β)`,
you should parametrize over `(F : Type*) [OrderRingIsoClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingIsoClass`. -/
structure OrderRingIso (α β : Type*) [Mul α] [Add α] [Mul β] [Add β] [LE α] [LE β] extends
  α ≃+* β where
  /-- The proposition that the function preserves the order bijectively. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b

@[inherit_doc]
infixl:25 " ≃+*o " => OrderRingIso

-- See module docstring for details

section Hom

variable [FunLike F α β]

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `RingHomClass F α β`
into an actual `OrderRingHom`.
This is declared as the default coercion from `F` to `α →+*o β`. -/
@[coe]
def OrderRingHomClass.toOrderRingHom [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
    [Preorder β] [OrderHomClass F α β] [RingHomClass F α β] (f : F) : α →+*o β :=
  { (f : α →+* β) with monotone' := OrderHomClass.monotone f }

/-- Any type satisfying `OrderRingHomClass` can be cast into `OrderRingHom` via
  `OrderRingHomClass.toOrderRingHom`. -/
instance [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]
    [OrderHomClass F α β] [RingHomClass F α β] : CoeTC F (α →+*o β) :=
  ⟨OrderRingHomClass.toOrderRingHom⟩

end Hom

section Equiv

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `RingEquivClass F α β`
into an actual `OrderRingIso`.
This is declared as the default coercion from `F` to `α ≃+*o β`. -/
@[coe]
def OrderRingIsoClass.toOrderRingIso [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
    [OrderIsoClass F α β] [RingEquivClass F α β] (f : F) : α ≃+*o β :=
  { (RingEquivClass.toRingEquiv f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f }

/-- Any type satisfying `OrderRingIsoClass` can be cast into `OrderRingIso` via
  `OrderRingIsoClass.toOrderRingIso`. -/
instance [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderIsoClass F α β]
    [RingEquivClass F α β] : CoeTC F (α ≃+*o β) :=
  ⟨OrderRingIsoClass.toOrderRingIso⟩

end Equiv

/-! ### Ordered ring homomorphisms -/

namespace OrderRingHom

variable [NonAssocSemiring α] [Preorder α]

section Preorder

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

/-- Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorphism. -/
def toOrderAddMonoidHom (f : α →+*o β) : α →+o β :=
  { f with }

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def toOrderMonoidWithZeroHom (f : α →+*o β) : α →*₀o β :=
  { f with }

instance : FunLike (α →+*o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective' h

instance : OrderHomClass (α →+*o β) α β where
  map_rel f _ _ h := f.monotone' h

instance : RingHomClass (α →+*o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

theorem toFun_eq_coe (f : α →+*o β) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem toRingHom_eq_coe (f : α →+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl

@[simp]
theorem toOrderAddMonoidHom_eq_coe (f : α →+*o β) : f.toOrderAddMonoidHom = f :=
  rfl

@[simp]
theorem toOrderMonoidWithZeroHom_eq_coe (f : α →+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl

@[simp]
theorem coe_coe_toRingHom (f : α →+*o β) : ⇑(f : α →+* β) = f :=
  rfl

@[deprecated (since := "2026-05-05")] alias coe_coe_ringHom := coe_coe_toRingHom

@[simp]
theorem coe_coe_orderAddMonoidHom (f : α →+*o β) : ⇑(f : α →+o β) = f :=
  rfl

@[simp]
theorem coe_coe_orderMonoidWithZeroHom (f : α →+*o β) : ⇑(f : α →*₀o β) = f :=
  rfl

@[norm_cast]
theorem coe_toRingHom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a :=
  rfl

@[deprecated (since := "2026-05-05")] alias coe_ringHom_apply := coe_toRingHom_apply

@[norm_cast]
theorem coe_orderAddMonoidHom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
  rfl

@[norm_cast]
theorem coe_orderMonoidWithZeroHom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a :=
  rfl

/-- Copy of an `OrderRingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

@[simp]
theorem coe_copy (f : α →+*o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : α →+*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- The identity as an ordered ring homomorphism. -/
protected def id : α →+*o α :=
  { RingHom.id _, OrderHom.id with }

instance : Inhabited (α →+*o α) :=
  ⟨OrderRingHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(OrderRingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : OrderRingHom.id α a = a :=
  rfl

@[simp]
theorem coe_toRingHom_id : (OrderRingHom.id α : α →+* α) = RingHom.id α :=
  rfl

@[deprecated (since := "2026-05-05")] alias coe_ringHom_id := coe_toRingHom_id

@[simp]
theorem coe_orderAddMonoidHom_id : (OrderRingHom.id α : α →+o α) = OrderAddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_orderMonoidWithZeroHom_id :
    (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl

/-- Composition of two `OrderRingHom`s as an `OrderRingHom`. -/
protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]
theorem coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) :=
  rfl

theorem comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →+*o β) : f.comp (OrderRingHom.id α) = f :=
  rfl

@[simp]
theorem id_comp (f : α →+*o β) : (OrderRingHom.id β).comp f = f :=
  rfl

@[simp]
theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, fun h => by rw [h]⟩

@[simp]
theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

variable [NonAssocSemiring β]

instance [Preorder β] : Preorder (OrderRingHom α β) :=
  Preorder.lift ((⇑) : _ → α → β)

instance [PartialOrder β] : PartialOrder (OrderRingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

end OrderRingHom

/-! ### Ordered ring isomorphisms -/


namespace OrderRingIso

section LE

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

/-- Reinterpret an ordered ring isomorphism as an order isomorphism. -/
@[coe]
def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩

instance : EquivLike (α ≃+*o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance : OrderIsoClass (α ≃+*o β) α β where
  map_le_map_iff f _ _ := f.map_le_map_iff'

instance : RingEquivClass (α ≃+*o β) α β where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

instance : CoeOut (α ≃+*o β) (α ≃+* β) where coe := toRingEquiv

theorem toFun_eq_coe (f : α ≃+*o β) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e :=
  rfl

@[simp]
theorem mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e :=
  ext fun _ => rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
theorem toRingEquiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f :=
  RingEquiv.ext fun _ => rfl

@[simp]
theorem toOrderIso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f :=
  OrderIso.ext rfl

@[simp]
theorem coe_toRingEquiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toOrderIso (f : α ≃+*o β) : DFunLike.coe (f : α ≃o β) = f :=
  rfl

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl]
protected def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, Iff.rfl⟩

instance : Inhabited (α ≃+*o α) :=
  ⟨OrderRingIso.refl α⟩

@[simp]
theorem refl_apply (x : α) : OrderRingIso.refl α x = x := by
  rfl

@[simp]
theorem coe_toRingEquiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α :=
  rfl

@[deprecated (since := "2026-05-05")] alias coe_ringEquiv_refl := coe_toRingEquiv_refl

@[simp]
theorem coe_orderIso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
  rfl

variable {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm]
protected def symm (e : α ≃+*o β) : β ≃+*o α :=
  ⟨e.toRingEquiv.symm, by
    intro a b
    erw [← map_le_map_iff e, e.1.apply_symm_apply, e.1.apply_symm_apply]⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : α ≃+*o β) : β → α :=
  e.symm

@[simp]
theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e := rfl

theorem symm_bijective : Bijective (OrderRingIso.symm : (α ≃+*o β) → β ≃+*o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_apply_apply (e : α ≃+*o β) (a : α) : e.symm (e a) = a :=
  e.toRingEquiv.symm_apply_apply a

@[simp]
theorem apply_symm_apply (e : α ≃+*o β) (b : β) : e (e.symm b) = b :=
  e.toRingEquiv.apply_symm_apply b

/-- Composition of `OrderRingIso`s as an `OrderRingIso`. -/
@[trans]
protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩

/-- This lemma used to be generated by [simps] on `trans`, but the lhs of this simplifies under
simp. Removed [simps] attribute and added aux version below. -/
theorem trans_toRingEquiv (f : α ≃+*o β) (g : β ≃+*o γ) :
    (OrderRingIso.trans f g).toRingEquiv = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

/-- `simp`-normal form of `trans_toRingEquiv`. -/
@[simp]
theorem trans_toRingEquiv_aux (f : α ≃+*o β) (g : β ≃+*o γ) :
    RingEquivClass.toRingEquiv (OrderRingIso.trans f g)
      = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

@[simp]
theorem trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) :=
  rfl

@[simp]
theorem self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α :=
  ext e.left_inv

@[simp]
theorem symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β :=
  ext e.right_inv

end LE

section Preorder

variable {R S : Type*} [Mul R] [Add R] [Mul S] [Add S] [Preorder R] [Preorder S]

theorem lt_symm_apply (e : R ≃+*o S) {x : R} {y : S} : x < e.symm y ↔ e x < y := by
  simpa using e.toOrderIso.lt_symm_apply

theorem symm_apply_lt (e : R ≃+*o S) {x : R} {y : S} : e.symm y < x ↔ y < e x := by
  simpa using e.toOrderIso.symm_apply_lt

end Preorder

section NonAssocSemiring

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

/-- Reinterpret an ordered ring isomorphism as an ordered ring homomorphism. -/
def toOrderRingHom (f : α ≃+*o β) : α →+*o β :=
  ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩

@[simp]
theorem toOrderRingHom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f :=
  rfl

@[simp, norm_cast]
theorem coe_toOrderRingHom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f :=
  rfl

@[simp]
theorem coe_toOrderRingHom_refl : (OrderRingIso.refl α : α →+*o α) = OrderRingHom.id α :=
  rfl

theorem toOrderRingHom_injective : Injective (toOrderRingHom : α ≃+*o β → α →+*o β) :=
  fun f g h => DFunLike.coe_injective <| by convert DFunLike.ext'_iff.1 h using 0

end NonAssocSemiring

end OrderRingIso
