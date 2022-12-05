/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Tactic.Basic

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

@[ext, to_additive]
theorem Monoid.ext {M : Type u} : ∀ ⦃m₁ m₂ : Monoid M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro
    @⟨@⟨⟨mul₁⟩⟩, ⟨one₁⟩, _, mul_one₁, npow₁, npow_zero₁, npow_succ₁⟩
    @⟨@⟨⟨mul₂⟩⟩, ⟨one₂⟩, one_mul₂, _, npow₂, npow_zero₂, npow_succ₂⟩ ⟨rfl⟩
  have : one₁ = one₂ := (one_mul₂ one₁).symm.trans (mul_one₁ one₂)
  have : npow₁ = npow₂ := by
    ext (n x)
    induction' n with n IH
    · rw [npow_zero₁, npow_zero₂, this]
    · rw [npow_succ₁, npow_succ₂, IH]
  congr
#align monoid.ext Monoid.ext

@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} : Function.Injective (@CommMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr
#align comm_monoid.to_monoid_injective CommMonoid.toMonoid_injective

@[ext, to_additive]
theorem CommMonoid.ext {M : Type _} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext

@[to_additive]
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h
#align left_cancel_monoid.to_monoid_injective LeftCancelMonoid.toMonoid_injective

@[ext, to_additive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align left_cancel_monoid.ext LeftCancelMonoid.ext

@[to_additive]
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h
#align right_cancel_monoid.to_monoid_injective RightCancelMonoid.toMonoid_injective

@[ext, to_additive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align right_cancel_monoid.ext RightCancelMonoid.ext

@[to_additive]
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr
#align cancel_monoid.to_left_cancel_monoid_injective CancelMonoid.toLeftCancelMonoid_injective

@[ext, to_additive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext

@[to_additive]
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  congr <;> {
    injection h with h'
    injection h' }
#align cancel_comm_monoid.to_comm_monoid_injective CancelCommMonoid.toCommMonoid_injective

@[ext, to_additive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext

-- set_option pp.all true

@[ext, to_additive]
theorem DivInvMonoid.ext {M : Type _} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : m₁.mul = m₂.mul)
  (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ := by
  have := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := by rw [this]
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have hpow : (@DivInvMonoid.toMonoid _ m₁).npow = (@DivInvMonoid.toMonoid _ m₂).npow :=
    congr_arg (@Monoid.npow M) (Monoid.ext h_mul)
  have hzpow : m₁.zpow = m₂.zpow := by
    ext (m x)
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have hdiv : m₁.div = m₂.div := by
    ext (a b)
    exact @map_div' M M
      (@MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass) m₁ m₂
      (@MonoidHom.monoidHomClass M M m₁.toMulOneClass m₂.toMulOneClass) f (congr_fun h_inv) a b
  rcases m₁ with @⟨_, ⟨inv₁⟩, ⟨div₁⟩, _, zpow₁⟩
  rcases m₂ with @⟨_, ⟨inv₂⟩, ⟨div₂⟩, _, zpow₂⟩
  congr
#align div_inv_monoid.ext DivInvMonoid.ext

@[ext, to_additive]
theorem Group.ext {G : Type _} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ := by
  /-let f :=
    @MonoidHom.mk' G G (by letI := g₁ <;> infer_instance) g₂ id fun a b =>
      congr_fun (congr_fun h_mul a) b
  exact
    Group.to_div_inv_monoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ (@Group.toDivisionMonoid _ g₂) f))-/
  --rintro @⟨toDivInvMonoid₁, mul_left_inv₁⟩ @⟨toDivInvMonoid₂, mul_left_inv₂⟩ h_mul
  --have : toDivInvMonoid₁.inv = toDivInvMonoid₂.inv := by
  --  sorry
  --have : toDivInvMonoid₁ = toDivInvMonoid₂ := DivInvMonoid.ext h_mul this
  have : g₁.inv = g₂.inv := by
    ext g
    rw [@inv_eq_iff_mul_eq_one _ g₁]
    show g₁.mul g (g₂.inv g) = 1 -- lean is using hMul and not mul
    rw [h_mul]
    rw [@mul_inv_eq_one _ g₂]
  have := DivInvMonoid.ext h_mul this
  cases g₁
  cases g₂
  congr
#align group.ext Group.ext

@[ext, to_additive]
theorem CommGroup.ext {G : Type _} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext
