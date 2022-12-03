/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Group

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `algebra.group.defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `monoid_hom.map_div`, `monoid_hom.map_pow` etc.

## Tags
monoid, group, extensionality
-/


universe u

@[ext, to_additive]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ := by
  have h₁ : (@Monoid.toMulOneClass _ m₁).one = (@Monoid.toMulOneClass _ m₂).one :=
    congr_arg (@MulOneClass.one M) (MulOneClass.ext h_mul)
  set f : @MonoidHom M M (@Monoid.toMulOneClass _ m₁) (@Monoid.toMulOneClass _ m₂) :=
    { toFun := id, map_one' := h₁, map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : m₁.npow = m₂.npow := by
    ext (n x)
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  cases m₁
  cases m₂
  congr <;> assumption
#align monoid.ext Monoid.ext

@[to_additive]
theorem CommMonoid.to_monoid_injective {M : Type u} : Function.Injective (@CommMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align comm_monoid.to_monoid_injective CommMonoid.to_monoid_injective

@[ext, to_additive]
theorem CommMonoid.ext {M : Type _} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.to_monoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext

@[to_additive]
theorem LeftCancelMonoid.to_monoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align left_cancel_monoid.to_monoid_injective LeftCancelMonoid.to_monoid_injective

@[ext, to_additive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  LeftCancelMonoid.to_monoid_injective <| Monoid.ext h_mul
#align left_cancel_monoid.ext LeftCancelMonoid.ext

@[to_additive]
theorem RightCancelMonoid.to_monoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align right_cancel_monoid.to_monoid_injective RightCancelMonoid.to_monoid_injective

@[ext, to_additive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  RightCancelMonoid.to_monoid_injective <| Monoid.ext h_mul
#align right_cancel_monoid.ext RightCancelMonoid.ext

@[to_additive]
theorem CancelMonoid.to_left_cancel_monoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align cancel_monoid.to_left_cancel_monoid_injective CancelMonoid.to_left_cancel_monoid_injective

@[ext, to_additive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.to_left_cancel_monoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext

@[to_additive]
theorem CancelCommMonoid.to_comm_monoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align cancel_comm_monoid.to_comm_monoid_injective CancelCommMonoid.to_comm_monoid_injective

@[ext, to_additive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.to_comm_monoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext

@[ext, to_additive]
theorem DivInvMonoid.ext {M : Type _} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : m₁.mul = m₂.mul)
    (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ := by
  have h₁ : (@DivInvMonoid.toMonoid _ m₁).one = (@DivInvMonoid.toMonoid _ m₂).one :=
    congr_arg (@Monoid.one M) (Monoid.ext h_mul)
  set f : @MonoidHom M M (by letI := m₁ <;> infer_instance) (by letI := m₂ <;> infer_instance) :=
    { toFun := id, map_one' := h₁, map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : (@DivInvMonoid.toMonoid _ m₁).npow = (@DivInvMonoid.toMonoid _ m₂).npow :=
    congr_arg (@Monoid.npow M) (Monoid.ext h_mul)
  have hzpow : m₁.zpow = m₂.zpow := by
    ext (m x)
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have hdiv : m₁.div = m₂.div := by
    ext (a b)
    exact @map_div' M M _ m₁ m₂ _ f (congr_fun h_inv) a b
  cases m₁
  cases m₂
  congr
  exacts[h_mul, h₁, hpow, h_inv, hdiv, hzpow]
#align div_inv_monoid.ext DivInvMonoid.ext

@[ext, to_additive]
theorem Group.ext {G : Type _} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ := by
  set f :=
    @MonoidHom.mk' G G (by letI := g₁ <;> infer_instance) g₂ id fun a b =>
      congr_fun (congr_fun h_mul a) b
  exact
    Group.to_div_inv_monoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ (@Group.toDivisionMonoid _ g₂) f))
#align group.ext Group.ext

@[ext, to_additive]
theorem CommGroup.ext {G : Type _} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.to_group_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext
