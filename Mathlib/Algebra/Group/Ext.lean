/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import Mathlib.Algebra.Hom.Group

#align_import algebra.group.ext from "leanprover-community/mathlib"@"e574b1a4e891376b0ef974b926da39e05da12a06"

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `Monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `Algebra.Group.Defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `MonoidHom.map_div`, `MonoidHom.map_pow` etc.

## Tags
monoid, group, extensionality
-/

universe u

@[to_additive (attr := ext)]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ := by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  -- ⊢ m₁ = m₂
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) (this)
  -- ⊢ m₁ = m₂
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := by
    ext n x
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  rcases m₁ with @⟨@⟨⟨_⟩⟩, ⟨_⟩⟩
  -- ⊢ mk one_mul✝ mul_one✝ npow✝ = m₂
  rcases m₂ with @⟨@⟨⟨_⟩⟩, ⟨_⟩⟩
  -- ⊢ mk one_mul✝¹ mul_one✝¹ npow✝¹ = mk one_mul✝ mul_one✝ npow✝
  congr
  -- 🎉 no goals
#align monoid.ext Monoid.ext
#align add_monoid.ext AddMonoid.ext

@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@CommMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  -- ⊢ mk mul_comm✝¹ = mk mul_comm✝
  congr
  -- 🎉 no goals
#align comm_monoid.to_monoid_injective CommMonoid.toMonoid_injective
#align add_comm_monoid.to_add_monoid_injective AddCommMonoid.toAddMonoid_injective

@[to_additive (attr := ext)]
theorem CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext
#align add_comm_monoid.ext AddCommMonoid.ext

@[to_additive]
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  -- ⊢ mk one_mul✝¹ mul_one✝¹ npow✝¹ = mk one_mul✝ mul_one✝ npow✝
  congr <;> injection h
            -- 🎉 no goals
            -- 🎉 no goals
            -- 🎉 no goals
#align left_cancel_monoid.to_monoid_injective LeftCancelMonoid.toMonoid_injective
#align add_left_cancel_monoid.to_add_monoid_injective AddLeftCancelMonoid.toAddMonoid_injective

@[to_additive (attr := ext)]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align left_cancel_monoid.ext LeftCancelMonoid.ext
#align add_left_cancel_monoid.ext AddLeftCancelMonoid.ext

@[to_additive]
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  -- ⊢ mk one_mul✝¹ mul_one✝¹ npow✝¹ = mk one_mul✝ mul_one✝ npow✝
  congr <;> injection h
            -- 🎉 no goals
            -- 🎉 no goals
            -- 🎉 no goals
#align right_cancel_monoid.to_monoid_injective RightCancelMonoid.toMonoid_injective
#align add_right_cancel_monoid.to_add_monoid_injective AddRightCancelMonoid.toAddMonoid_injective

@[to_additive (attr := ext)]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align right_cancel_monoid.ext RightCancelMonoid.ext
#align add_right_cancel_monoid.ext AddRightCancelMonoid.ext

@[to_additive]
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  -- ⊢ mk mul_right_cancel✝¹ = mk mul_right_cancel✝
  congr
  -- 🎉 no goals
#align cancel_monoid.to_left_cancel_monoid_injective CancelMonoid.toLeftCancelMonoid_injective
#align add_cancel_monoid.to_left_cancel_add_monoid_injective AddCancelMonoid.toAddLeftCancelMonoid_injective

@[to_additive (attr := ext)]
theorem CancelMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext
#align add_cancel_monoid.ext AddCancelMonoid.ext

@[to_additive]
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  -- ⊢ mk mul_comm✝¹ = mk mul_comm✝
  congr <;> {
    injection h with h'
    injection h' }
#align cancel_comm_monoid.to_comm_monoid_injective CancelCommMonoid.toCommMonoid_injective
#align add_cancel_comm_monoid.to_add_comm_monoid_injective AddCancelCommMonoid.toAddCommMonoid_injective

@[to_additive (attr := ext)]
theorem CancelCommMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext
#align add_cancel_comm_monoid.ext AddCancelCommMonoid.ext

@[to_additive (attr := ext)]
theorem DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : m₁.mul = m₂.mul)
  (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  -- ⊢ m₁ = m₂
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  -- ⊢ m₁ = m₂
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := congr_arg (·.npow) h_mon
  -- ⊢ m₁ = m₂
  have : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext a b
    exact @map_div' _ _
      (@MonoidHom _ _ (_) _) (id _) _
      (@MonoidHom.monoidHomClass _ _ (_) _) f (congr_fun h_inv) a b
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  -- ⊢ mk zpow✝ = m₂
  rcases m₂ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  -- ⊢ mk zpow✝¹ = mk zpow✝
  congr
  -- 🎉 no goals
#align div_inv_monoid.ext DivInvMonoid.ext
#align sub_neg_monoid.ext SubNegMonoid.ext

@[to_additive (attr := ext)]
theorem Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  -- ⊢ g₁ = g₂
  let f : @MonoidHom G G g₁.toMulOneClass g₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ g₂.toDivisionMonoid f))
#align group.ext Group.ext
#align add_group.ext AddGroup.ext

@[to_additive (attr := ext)]
theorem CommGroup.ext {G : Type*} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext
#align add_comm_group.ext AddCommGroup.ext
