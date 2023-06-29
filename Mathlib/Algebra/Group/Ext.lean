/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.group.ext
! leanprover-community/mathlib commit e574b1a4e891376b0ef974b926da39e05da12a06
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Group.PPow

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

variable [Monoid M]

@[to_additive (attr := ext)]
theorem Semigroup.ext {M : Type u} ⦃m₁ m₂ : Semigroup M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ := by
  let f := @MulHom.mk _ _ m₁.toMul m₂.toMul id fun _ _ => congr_fun (congr_fun h_mul _) _
  have : m₁.ppow = m₂.ppow := by
    ext n hn x
    exact @map_ppow _ M M m₁ m₂ _ f x ⟨n, hn⟩
  rcases m₁ with @⟨@⟨_⟩, _⟩
  rcases m₂ with @⟨@⟨_⟩, _⟩
  congr
#align semigroup.ext Semigroup.extₓ
#noalign semigroup.ext_iff
#align add_semigroup.ext AddSemigroup.extₓ
#noalign add_semigroup.ext_iff

@[to_additive]
theorem CommSemigroup.toSemigroup_injective {M : Type u} [Semigroup M] :
    Function.Injective (@CommSemigroup.toSemigroup M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
theorem CommSemigroup.ext {M : Type _} ⦃m₁ m₂ : CommSemigroup M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CommSemigroup.toSemigroup_injective <| Semigroup.ext h_mul
#align comm_semigroup.ext CommSemigroup.extₓ
#noalign comm_semigroup.ext_iff
#align add_comm_semigroup.ext AddCommSemigroup.extₓ
#noalign add_comm_semigroup.ext_iff

@[to_additive (attr := ext)]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ := by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) (this)
  have h₂ : m₁.toSemigroup = m₂.toSemigroup := Semigroup.ext h_mul
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := by
    ext n x
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  rcases m₁ with @⟨_, ⟨_⟩⟩
  rcases m₂ with @⟨_, ⟨_⟩⟩
  congr
#align monoid.ext Monoid.ext
#align add_monoid.ext AddMonoid.ext

@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@CommMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr
#align comm_monoid.to_monoid_injective CommMonoid.toMonoid_injective
#align add_comm_monoid.to_add_monoid_injective AddCommMonoid.toAddMonoid_injective

@[to_additive (attr := ext)]
theorem CommMonoid.ext {M : Type _} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext
#align add_comm_monoid.ext AddCommMonoid.ext

@[to_additive]
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h
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
  congr <;> injection h
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
  congr
#align cancel_monoid.to_left_cancel_monoid_injective CancelMonoid.toLeftCancelMonoid_injective
#align add_cancel_monoid.to_left_cancel_add_monoid_injective AddCancelMonoid.toAddLeftCancelMonoid_injective

@[to_additive (attr := ext)]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext
#align add_cancel_monoid.ext AddCancelMonoid.ext

@[to_additive]
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  congr <;> {
    injection h with h'
    injection h' }
#align cancel_comm_monoid.to_comm_monoid_injective CancelCommMonoid.toCommMonoid_injective
#align add_cancel_comm_monoid.to_add_comm_monoid_injective AddCancelCommMonoid.toAddCommMonoid_injective

@[to_additive (attr := ext)]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext
#align add_cancel_comm_monoid.ext AddCancelCommMonoid.ext

@[to_additive (attr := ext)]
theorem DivInvMonoid.ext {M : Type _} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : m₁.mul = m₂.mul)
  (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := congr_arg (·.npow) h_mon
  have : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext a b
    exact @map_div' _ _
      (@MonoidHom _ _ (_) _) (id _) _
      (@MonoidHom.monoidHomClass _ _ (_) _) f (congr_fun h_inv) a b
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  rcases m₂ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  congr
#align div_inv_monoid.ext DivInvMonoid.ext
#align sub_neg_monoid.ext SubNegMonoid.ext

@[to_additive (attr := ext)]
theorem Group.ext {G : Type _} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
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
theorem CommGroup.ext {G : Type _} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext
#align add_comm_group.ext AddCommGroup.ext
