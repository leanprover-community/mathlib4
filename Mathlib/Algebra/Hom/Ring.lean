/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Pi.Algebra
import Mathlib.Algebra.Hom.Units
import Mathlib.Data.Set.Image

#align_import algebra.hom.ring from "leanprover-community/mathlib"@"cf9386b56953fb40904843af98b7a80757bbe7f9"

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `RingHom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

## Main definitions

* `NonUnitalRingHom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `RingHom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notations

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `SemiringHom` -- the idea is that `RingHom` is used.
  The constructor for a `RingHom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `RingHom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`RingHom`, `SemiringHom`
-/


open Function

variable {F α β γ : Type*}

/-- Bundled non-unital semiring homomorphisms `α →ₙ+* β`; use this for bundled non-unital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : α →ₙ+* β)`,
you should parametrize over `(F : Type*) [NonUnitalRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `NonUnitalRingHomClass`. -/
structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β
#align non_unital_ring_hom NonUnitalRingHom

/-- `α →ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →ₙ+* " => NonUnitalRingHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as a semigroup
homomorphism `α →ₙ* β`. The `simp`-normal form is `(f : α →ₙ* β)`. -/
add_decl_doc NonUnitalRingHom.toMulHom
#align non_unital_ring_hom.to_mul_hom NonUnitalRingHom.toMulHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as an additive
monoid homomorphism `α →+ β`. The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc NonUnitalRingHom.toAddMonoidHom
#align non_unital_ring_hom.to_add_monoid_hom NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

/-- `NonUnitalRingHomClass F α β` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `NonUnitalRingHom`. -/
class NonUnitalRingHomClass (F : Type*) (α β : outParam (Type*)) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends MulHomClass F α β, AddMonoidHomClass F α β
#align non_unital_ring_hom_class NonUnitalRingHomClass

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalRingHomClass F α β]

/-- Turn an element of a type `F` satisfying `NonUnitalRingHomClass F α β` into an actual
`NonUnitalRingHom`. This is declared as the default coercion from `F` to `α →ₙ+* β`. -/
@[coe]
def NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α →ₙ+* β :=
  { (f : α →ₙ* β), (f : α →+ β) with }

/-- Any type satisfying `NonUnitalRingHomClass` can be cast into `NonUnitalRingHom` via
`NonUnitalRingHomClass.toNonUnitalRingHom`. -/
instance : CoeTC F (α →ₙ+* β) :=
  ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    -- ⊢ { toMulHom := toMulHom✝, map_zero' := map_zero'✝, map_add' := map_add'✝ } = g
    cases g
    -- ⊢ { toMulHom := toMulHom✝¹, map_zero' := map_zero'✝¹, map_add' := map_add'✝¹ } …
    congr
    -- ⊢ toMulHom✝¹ = toMulHom✝
    apply FunLike.coe_injective'
    -- ⊢ ↑toMulHom✝¹ = ↑toMulHom✝
    exact h
    -- 🎉 no goals
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

-- Porting note:
-- These helper instances are unhelpful in Lean 4, so omitting:
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
-- directly. -/
-- instance : CoeFun (α →ₙ+* β) fun _ => α → β :=
--   ⟨fun f => f.toFun⟩

-- Porting note: removed due to new `coe` in Lean4
#noalign non_unital_ring_hom.to_fun_eq_coe
#noalign non_unital_ring_hom.coe_mk
#noalign non_unital_ring_hom.coe_coe

initialize_simps_projections NonUnitalRingHom (toFun → apply)

@[simp]
theorem coe_toMulHom (f : α →ₙ+* β) : ⇑f.toMulHom = f :=
  rfl
#align non_unital_ring_hom.coe_to_mul_hom NonUnitalRingHom.coe_toMulHom

@[simp]
theorem coe_mulHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ :=
  rfl
#align non_unital_ring_hom.coe_mul_hom_mk NonUnitalRingHom.coe_mulHom_mk

theorem coe_toAddMonoidHom (f : α →ₙ+* β) : ⇑f.toAddMonoidHom = f := rfl
#align non_unital_ring_hom.coe_to_add_monoid_hom NonUnitalRingHom.coe_toAddMonoidHom

@[simp]
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨⟨f, h₂⟩, h₃⟩ :=
  rfl
#align non_unital_ring_hom.coe_add_monoid_hom_mk NonUnitalRingHom.coe_addMonoidHom_mk

/-- Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }
#align non_unital_ring_hom.copy NonUnitalRingHom.copy

@[simp]
theorem coe_copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align non_unital_ring_hom.coe_copy NonUnitalRingHom.coe_copy

theorem copy_eq (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align non_unital_ring_hom.copy_eq NonUnitalRingHom.copy_eq

end coe

section

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]
variable (f : α →ₙ+* β) {x y : α}

@[ext]
theorem ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g :=
  FunLike.ext _ _
#align non_unital_ring_hom.ext NonUnitalRingHom.ext

theorem ext_iff {f g : α →ₙ+* β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align non_unital_ring_hom.ext_iff NonUnitalRingHom.ext_iff

@[simp]
theorem mk_coe (f : α →ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk (MulHom.mk f h₁) h₂ h₃ = f :=
  ext fun _ => rfl
#align non_unital_ring_hom.mk_coe NonUnitalRingHom.mk_coe

theorem coe_addMonoidHom_injective : Injective fun f : α →ₙ+* β => (f : α →+ β) :=
  fun _ _ h => ext <| FunLike.congr_fun (F := α →+ β) h
#align non_unital_ring_hom.coe_add_monoid_hom_injective NonUnitalRingHom.coe_addMonoidHom_injective

set_option linter.deprecated false in
theorem coe_mulHom_injective : Injective fun f : α →ₙ+* β => (f : α →ₙ* β) := fun _ _ h =>
  ext <| MulHom.congr_fun h
#align non_unital_ring_hom.coe_mul_hom_injective NonUnitalRingHom.coe_mulHom_injective

end

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
protected def id (α : Type*) [NonUnitalNonAssocSemiring α] : α →ₙ+* α := by
  refine' { toFun := id.. } <;> intros <;> rfl
                                -- ⊢ id (x✝ * y✝) = id x✝ * id y✝
                                -- ⊢ MulHom.toFun { toFun := id, map_mul' := (_ : ∀ (x y : α), id (x * y) = id x  …
                                -- ⊢ MulHom.toFun { toFun := id, map_mul' := (_ : ∀ (x y : α), id (x * y) = id x  …
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align non_unital_ring_hom.id NonUnitalRingHom.id

instance : Zero (α →ₙ+* β) :=
  ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩

instance : Inhabited (α →ₙ+* β) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : α →ₙ+* β) = 0 :=
  rfl
#align non_unital_ring_hom.coe_zero NonUnitalRingHom.coe_zero

@[simp]
theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 :=
  rfl
#align non_unital_ring_hom.zero_apply NonUnitalRingHom.zero_apply

@[simp]
theorem id_apply (x : α) : NonUnitalRingHom.id α x = x :=
  rfl
#align non_unital_ring_hom.id_apply NonUnitalRingHom.id_apply

@[simp]
theorem coe_addMonoidHom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl
#align non_unital_ring_hom.coe_add_monoid_hom_id NonUnitalRingHom.coe_addMonoidHom_id

@[simp]
theorem coe_mulHom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α :=
  rfl
#align non_unital_ring_hom.coe_mul_hom_id NonUnitalRingHom.coe_mulHom_id

variable [NonUnitalNonAssocSemiring γ]

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }
#align non_unital_ring_hom.comp NonUnitalRingHom.comp

/-- Composition of non-unital ring homomorphisms is associative. -/
theorem comp_assoc {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α →ₙ+* β) (g : β →ₙ+* γ)
    (h : γ →ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align non_unital_ring_hom.comp_assoc NonUnitalRingHom.comp_assoc

@[simp]
theorem coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align non_unital_ring_hom.coe_comp NonUnitalRingHom.coe_comp

@[simp]
theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) :=
  rfl
#align non_unital_ring_hom.comp_apply NonUnitalRingHom.comp_apply
variable (g : β →ₙ+* γ) (f : α →ₙ+* β)

@[simp]
theorem coe_comp_addMonoidHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    AddMonoidHom.mk ⟨g ∘ f, (g.comp f).map_zero'⟩ (g.comp f).map_add' = (g : β →+ γ).comp f :=
  rfl
#align non_unital_ring_hom.coe_comp_add_monoid_hom NonUnitalRingHom.coe_comp_addMonoidHom

@[simp]
theorem coe_comp_mulHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    MulHom.mk (g ∘ f) (g.comp f).map_mul' = (g : β →ₙ* γ).comp f :=
  rfl
#align non_unital_ring_hom.coe_comp_mul_hom NonUnitalRingHom.coe_comp_mulHom

@[simp]
theorem comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by
  ext
  -- ⊢ ↑(comp g 0) x✝ = ↑0 x✝
  simp
  -- 🎉 no goals
#align non_unital_ring_hom.comp_zero NonUnitalRingHom.comp_zero

@[simp]
theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  -- ⊢ ↑(comp 0 f) x✝ = ↑0 x✝
  rfl
  -- 🎉 no goals
#align non_unital_ring_hom.zero_comp NonUnitalRingHom.zero_comp

@[simp]
theorem comp_id (f : α →ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f :=
  ext fun _ => rfl
#align non_unital_ring_hom.comp_id NonUnitalRingHom.comp_id

@[simp]
theorem id_comp (f : α →ₙ+* β) : (NonUnitalRingHom.id β).comp f = f :=
  ext fun _ => rfl
#align non_unital_ring_hom.id_comp NonUnitalRingHom.id_comp

instance : MonoidWithZero (α →ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc f g h := comp_assoc _ _ _
  zero := 0
  mul_zero := comp_zero
  zero_mul := zero_comp

theorem one_def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α :=
  rfl
#align non_unital_ring_hom.one_def NonUnitalRingHom.one_def

@[simp]
theorem coe_one : ⇑(1 : α →ₙ+* α) = id :=
  rfl
#align non_unital_ring_hom.coe_one NonUnitalRingHom.coe_one

theorem mul_def (f g : α →ₙ+* α) : f * g = f.comp g :=
  rfl
#align non_unital_ring_hom.mul_def NonUnitalRingHom.mul_def

@[simp]
theorem coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g :=
  rfl
#align non_unital_ring_hom.coe_mul NonUnitalRingHom.coe_mul

theorem cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩
#align non_unital_ring_hom.cancel_right NonUnitalRingHom.cancel_right

theorem cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩
                                  -- 🎉 no goals
#align non_unital_ring_hom.cancel_left NonUnitalRingHom.cancel_left

end NonUnitalRingHom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a
sensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`. -/
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β
#align ring_hom RingHom

/-- `α →+* β` denotes the type of ring homomorphisms from `α` to `β`. -/
infixr:25 " →+* " => RingHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid with zero homomorphism `α →*₀ β`.
The `simp`-normal form is `(f : α →*₀ β)`. -/
add_decl_doc RingHom.toMonoidWithZeroHom
#align ring_hom.to_monoid_with_zero_hom RingHom.toMonoidWithZeroHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid homomorphism `α →* β`.
The `simp`-normal form is `(f : α →* β)`. -/
add_decl_doc RingHom.toMonoidHom
#align ring_hom.to_monoid_hom RingHom.toMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as an additive monoid homomorphism `α →+ β`.
The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc RingHom.toAddMonoidHom
#align ring_hom.to_add_monoid_hom RingHom.toAddMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a non-unital ring homomorphism `α →ₙ+* β`. The
`simp`-normal form is `(f : α →ₙ+* β)`. -/
add_decl_doc RingHom.toNonUnitalRingHom
#align ring_hom.to_non_unital_ring_hom RingHom.toNonUnitalRingHom

section RingHomClass

/-- `RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `RingHom`.

This extends from both `MonoidHomClass` and `MonoidWithZeroHomClass` in
order to put the fields in a sensible order, even though
`MonoidWithZeroHomClass` already extends `MonoidHomClass`. -/
class RingHomClass (F : Type*) (α β : outParam (Type*)) [NonAssocSemiring α]
  [NonAssocSemiring β] extends MonoidHomClass F α β, AddMonoidHomClass F α β,
  MonoidWithZeroHomClass F α β
#align ring_hom_class RingHomClass

set_option linter.deprecated false in
/-- Ring homomorphisms preserve `bit1`. -/
@[simp] lemma map_bit1 [NonAssocSemiring α] [NonAssocSemiring β] [RingHomClass F α β]
    (f : F) (a : α) : (f (bit1 a) : β) = bit1 (f a) := by simp [bit1]
                                                          -- 🎉 no goals
#align map_bit1 map_bit1

-- Porting note: marked `{}` rather than `[]` to prevent dangerous instances
variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} [RingHomClass F α β]

/-- Turn an element of a type `F` satisfying `RingHomClass F α β` into an actual
`RingHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

/-- Any type satisfying `RingHomClass` can be cast into `RingHom` via `RingHomClass.toRingHom`. -/
instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩

instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }
#align ring_hom_class.to_non_unital_ring_hom_class RingHomClass.toNonUnitalRingHomClass

end RingHomClass

namespace RingHom

section coe

/-!
Throughout this section, some `Semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

instance instRingHomClass : RingHomClass (α →+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    -- ⊢ { toMonoidHom := toMonoidHom✝, map_zero' := map_zero'✝, map_add' := map_add' …
    cases g
    -- ⊢ { toMonoidHom := toMonoidHom✝¹, map_zero' := map_zero'✝¹, map_add' := map_ad …
    congr
    -- ⊢ toMonoidHom✝¹ = toMonoidHom✝
    apply FunLike.coe_injective'
    -- ⊢ ↑toMonoidHom✝¹ = ↑toMonoidHom✝
    exact h
    -- 🎉 no goals
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

-- Porting note:
-- These helper instances are unhelpful in Lean 4, so omitting:
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
-- directly.
-- -/
-- instance : CoeFun (α →+* β) fun _ => α → β :=
--   ⟨RingHom.toFun⟩

initialize_simps_projections RingHom (toFun → apply)

-- Porting note: is this lemma still needed in Lean4?
-- Porting note: because `f.toFun` really means `f.toMonoidHom.toOneHom.toFun` and
-- `toMonoidHom_eq_coe` wants to simplify `f.toMonoidHom` to `(↑f : M →* N)`, this can't
-- be a simp lemma anymore
-- @[simp]
theorem toFun_eq_coe (f : α →+* β) : f.toFun = f :=
  rfl
#align ring_hom.to_fun_eq_coe RingHom.toFun_eq_coe

@[simp]
theorem coe_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α → β) = f :=
  rfl
#align ring_hom.coe_mk RingHom.coe_mk

@[simp]
theorem coe_coe {F : Type*} [RingHomClass F α β] (f : F) : ((f : α →+* β) : α → β) = f :=
  rfl
#align ring_hom.coe_coe RingHom.coe_coe

attribute [coe] RingHom.toMonoidHom

instance coeToMonoidHom : Coe (α →+* β) (α →* β) :=
  ⟨RingHom.toMonoidHom⟩
#align ring_hom.has_coe_monoid_hom RingHom.coeToMonoidHom

-- Porting note: `dsimp only` can prove this
#noalign ring_hom.coe_monoid_hom

@[simp]
theorem toMonoidHom_eq_coe (f : α →+* β) : f.toMonoidHom = f :=
  rfl
#align ring_hom.to_monoid_hom_eq_coe RingHom.toMonoidHom_eq_coe

-- Porting note: this can't be a simp lemma anymore
-- @[simp]
theorem toMonoidWithZeroHom_eq_coe (f : α →+* β) : (f.toMonoidWithZeroHom : α → β) = f := by
  rfl
  -- 🎉 no goals
#align ring_hom.to_monoid_with_zero_hom_eq_coe RingHom.toMonoidWithZeroHom_eq_coe

@[simp]
theorem coe_monoidHom_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α →* β) = f :=
  rfl
#align ring_hom.coe_monoid_hom_mk RingHom.coe_monoidHom_mk

-- Porting note: `dsimp only` can prove this
#noalign ring_hom.coe_add_monoid_hom

@[simp]
theorem toAddMonoidHom_eq_coe (f : α →+* β) : f.toAddMonoidHom = f :=
  rfl
#align ring_hom.to_add_monoid_hom_eq_coe RingHom.toAddMonoidHom_eq_coe

@[simp]
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨⟨f, h₃⟩, h₄⟩ :=
  rfl
#align ring_hom.coe_add_monoid_hom_mk RingHom.coe_addMonoidHom_mk

/-- Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }
#align ring_hom.copy RingHom.copy

@[simp]
theorem coe_copy (f : α →+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align ring_hom.coe_copy RingHom.coe_copy

theorem copy_eq (f : α →+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align ring_hom.copy_eq RingHom.copy_eq

end coe

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β) {x y : α}

theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x
#align ring_hom.congr_fun RingHom.congr_fun

theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h
#align ring_hom.congr_arg RingHom.congr_arg

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h
#align ring_hom.coe_inj RingHom.coe_inj

@[ext]
theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g :=
  FunLike.ext _ _
#align ring_hom.ext RingHom.ext

theorem ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align ring_hom.ext_iff RingHom.ext_iff

@[simp]
theorem mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f :=
  ext fun _ => rfl
#align ring_hom.mk_coe RingHom.mk_coe

theorem coe_addMonoidHom_injective : Injective (fun f : α →+* β => (f : α →+ β)) := fun _ _ h =>
  ext <| FunLike.congr_fun (F := α →+ β) h
#align ring_hom.coe_add_monoid_hom_injective RingHom.coe_addMonoidHom_injective

set_option linter.deprecated false in
theorem coe_monoidHom_injective : Injective (fun f : α →+* β => (f : α →* β)) := fun _ _ h =>
  ext <| MonoidHom.congr_fun h
#align ring_hom.coe_monoid_hom_injective RingHom.coe_monoidHom_injective

/-- Ring homomorphisms map zero to zero. -/
protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
  map_zero f
#align ring_hom.map_zero RingHom.map_zero

/-- Ring homomorphisms map one to one. -/
protected theorem map_one (f : α →+* β) : f 1 = 1 :=
  map_one f
#align ring_hom.map_one RingHom.map_one

/-- Ring homomorphisms preserve addition. -/
protected theorem map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b :=
  map_add f
#align ring_hom.map_add RingHom.map_add

/-- Ring homomorphisms preserve multiplication. -/
protected theorem map_mul (f : α →+* β) : ∀ a b, f (a * b) = f a * f b :=
  map_mul f
#align ring_hom.map_mul RingHom.map_mul

@[simp]
theorem map_ite_zero_one {F : Type*} [RingHomClass F α β] (f : F) (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp [h]
  -- ⊢ ↑f (if p then 0 else 1) = 0
                       -- 🎉 no goals
                       -- 🎉 no goals
#align ring_hom.map_ite_zero_one RingHom.map_ite_zero_one

@[simp]
theorem map_ite_one_zero {F : Type*} [RingHomClass F α β] (f : F) (p : Prop) [Decidable p] :
    f (ite p 1 0) = ite p 1 0 := by
  split_ifs with h <;> simp [h]
  -- ⊢ ↑f (if p then 1 else 0) = 1
                       -- 🎉 no goals
                       -- 🎉 no goals
#align ring_hom.map_ite_one_zero RingHom.map_ite_one_zero

/-- `f : α →+* β` has a trivial codomain iff `f 1 = 0`. -/
theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by rw [map_one, eq_comm]
                                                                           -- 🎉 no goals
#align ring_hom.codomain_trivial_iff_map_one_eq_zero RingHom.codomain_trivial_iff_map_one_eq_zero

/-- `f : α →+* β` has a trivial codomain iff it has a trivial range. -/
theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩
                   -- 🎉 no goals
#align ring_hom.codomain_trivial_iff_range_trivial RingHom.codomain_trivial_iff_range_trivial

/-- `f : α →+* β` has a trivial codomain iff its range is `{0}`. -/
theorem codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ Set.range f = {0} :=
  f.codomain_trivial_iff_range_trivial.trans
    ⟨fun h =>
      Set.ext fun y => ⟨fun ⟨x, hx⟩ => by simp [← hx, h x], fun hy => ⟨0, by simpa using hy.symm⟩⟩,
                                          -- 🎉 no goals
                                                                             -- 🎉 no goals
      fun h x => Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self x)⟩
#align ring_hom.codomain_trivial_iff_range_eq_singleton_zero RingHom.codomain_trivial_iff_range_eq_singleton_zero

/-- `f : α →+* β` doesn't map `1` to `0` if `β` is nontrivial -/
theorem map_one_ne_zero [Nontrivial β] : f 1 ≠ 0 :=
  mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one
#align ring_hom.map_one_ne_zero RingHom.map_one_ne_zero

/-- If there is a homomorphism `f : α →+* β` and `β` is nontrivial, then `α` is nontrivial. -/
theorem domain_nontrivial [Nontrivial β] : Nontrivial α :=
  ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, map_zero]) f.map_one_ne_zero⟩⟩
                                       -- 🎉 no goals
#align ring_hom.domain_nontrivial RingHom.domain_nontrivial

theorem codomain_trivial (f : α →+* β) [h : Subsingleton α] : Subsingleton β :=
  (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial
#align ring_hom.codomain_trivial RingHom.codomain_trivial

end

/-- Ring homomorphisms preserve additive inverse. -/
protected theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x :=
  map_neg f x
#align ring_hom.map_neg RingHom.map_neg

/-- Ring homomorphisms preserve subtraction. -/
protected theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) :
    f (x - y) = f x - f y :=
  map_sub f x y
#align ring_hom.map_sub RingHom.map_sub

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' [NonAssocSemiring α] [NonAssocRing β] (f : α →* β)
    (map_add : ∀ a b, f (a + b) = f a + f b) : α →+* β :=
  { AddMonoidHom.mk' f map_add, f with }
#align ring_hom.mk' RingHom.mk'

section Semiring

variable [Semiring α] [Semiring β]

theorem isUnit_map (f : α →+* β) {a : α} : IsUnit a → IsUnit (f a) :=
  IsUnit.map f
#align ring_hom.is_unit_map RingHom.isUnit_map

protected theorem map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f
#align ring_hom.map_dvd RingHom.map_dvd

end Semiring

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type*) [NonAssocSemiring α] : α →+* α := by
  refine' { toFun := _root_.id.. } <;> intros <;> rfl
                                       -- ⊢ _root_.id 1 = 1
                                       -- ⊢ OneHom.toFun { toFun := _root_.id, map_one' := ?refine'_1 } (x✝ * y✝) = OneH …
                                       -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := _root_.id, map_one' := ?refine'_1 }, …
                                       -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := _root_.id, map_one' := ?refine'_1 }, …
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align ring_hom.id RingHom.id

instance : Inhabited (α →+* α) :=
  ⟨id α⟩

@[simp]
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl
#align ring_hom.id_apply RingHom.id_apply

@[simp]
theorem coe_addMonoidHom_id : (id α : α →+ α) = AddMonoidHom.id α :=
  rfl
#align ring_hom.coe_add_monoid_hom_id RingHom.coe_addMonoidHom_id

@[simp]
theorem coe_monoidHom_id : (id α : α →* α) = MonoidHom.id α :=
  rfl
#align ring_hom.coe_monoid_hom_id RingHom.coe_monoidHom_id

variable {_ : NonAssocSemiring γ}

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun := g ∘ f, map_one' := by simp }
                                                                                       -- 🎉 no goals
#align ring_hom.comp RingHom.comp

/-- Composition of semiring homomorphisms is associative. -/
theorem comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align ring_hom.comp_assoc RingHom.comp_assoc

@[simp]
theorem coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn :=
  rfl
#align ring_hom.coe_comp RingHom.coe_comp

theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) :
    (hnp.comp hmn : α → γ) x = hnp (hmn x) :=
  rfl
#align ring_hom.comp_apply RingHom.comp_apply

@[simp]
theorem comp_id (f : α →+* β) : f.comp (id α) = f :=
  ext fun _ => rfl
#align ring_hom.comp_id RingHom.comp_id

@[simp]
theorem id_comp (f : α →+* β) : (id β).comp f = f :=
  ext fun _ => rfl
#align ring_hom.id_comp RingHom.id_comp

instance : Monoid (α →+* α) where
  one := id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc f g h := comp_assoc _ _ _

theorem one_def : (1 : α →+* α) = id α :=
  rfl
#align ring_hom.one_def RingHom.one_def

theorem mul_def (f g : α →+* α) : f * g = f.comp g :=
  rfl
#align ring_hom.mul_def RingHom.mul_def

@[simp]
theorem coe_one : ⇑(1 : α →+* α) = _root_.id :=
  rfl
#align ring_hom.coe_one RingHom.coe_one

@[simp]
theorem coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g :=
  rfl
#align ring_hom.coe_mul RingHom.coe_mul

theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩
#align ring_hom.cancel_right RingHom.cancel_right

theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => RingHom.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩
                                          -- 🎉 no goals
#align ring_hom.cancel_left RingHom.cancel_left

end RingHom

/-- Pullback `IsDomain` instance along an injective function. -/
protected theorem Function.Injective.isDomain [Ring α] [IsDomain α] [Ring β] (f : β →+* α)
    (hf : Injective f) : IsDomain β := by
  haveI := pullback_nonzero f f.map_zero f.map_one
  -- ⊢ IsDomain β
  haveI := IsRightCancelMulZero.to_noZeroDivisors α
  -- ⊢ IsDomain β
  haveI := hf.noZeroDivisors f f.map_zero f.map_mul
  -- ⊢ IsDomain β
  exact NoZeroDivisors.to_isDomain β
  -- 🎉 no goals
#align function.injective.is_domain Function.Injective.isDomain

namespace AddMonoidHom

variable [CommRing α] [IsDomain α] [CommRing β] (f : β →+ α)

-- Porting note: there's some disagreement over the naming scheme here.
-- This could perhaps be `mkRingHom_of_mul_self_of_two_ne_zero`.
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/naming.20conventions/near/315558410
/-- Make a ring homomorphism from an additive group homomorphism from a commutative ring to an
integral domain that commutes with self multiplication, assumes that two is nonzero and `1` is sent
to `1`. -/
def mkRingHomOfMulSelfOfTwoNeZero (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0)
    (h_one : f 1 = 1) : β →+* α :=
  { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      -- ⊢ OneHom.toFun { toFun := f.toFun, map_one' := h_one } (x * y) = OneHom.toFun  …
      rw [mul_add, add_mul, add_mul, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mul,
        mul_add, mul_add, ← sub_eq_zero, add_comm (f x * f x + f (y * x)), ← sub_sub, ← sub_sub,
        ← sub_sub, mul_comm y x, mul_comm (f y) (f x)] at hxy
      simp only [add_assoc, add_sub_assoc, add_sub_cancel'_right] at hxy
      -- ⊢ OneHom.toFun { toFun := f.toFun, map_one' := h_one } (x * y) = OneHom.toFun  …
      rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero (M₀ := α),
        sub_eq_zero, or_iff_not_imp_left] at hxy
      exact hxy h_two }
      -- 🎉 no goals
#align add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero

@[simp]
theorem coe_fn_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β → α) = f :=
  rfl
#align add_monoid_hom.coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero

-- Porting note: `simp` can prove this
-- @[simp]
theorem coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β →+ α) = f := by
  ext
  -- ⊢ ↑↑(mkRingHomOfMulSelfOfTwoNeZero f h h_two h_one) x✝ = ↑f x✝
  rfl
  -- 🎉 no goals
#align add_monoid_hom.coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero AddMonoidHom.coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero

end AddMonoidHom
