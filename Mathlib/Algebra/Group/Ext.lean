/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `Monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `Algebra.Group.Defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `MonoidHom.map_div`, `MonoidHom.map_pow` etc.

To refer to the `*` operator of a particular instance `i`, we use
`(letI := i; HMul.hMul : M → M → M)` instead of `i.mul` (which elaborates to `Mul.mul`), as the
former uses `HMul.hMul` which is the canonical spelling.

## Tags
monoid, group, extensionality
-/

assert_not_exists MonoidWithZero DenselyOrdered

open Function

universe u

@[to_additive (attr := ext)]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ := by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) this
  let f : @MonoidHom M M m₁.toMul m₁.toOne m₂.toMul m₂.toOne :=
    @MonoidHom.mk M M m₁.toMul m₁.toOne m₂.toMul m₂.toOne
      (@OneHom.mk _ _ m₁.toOne m₂.toOne id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := by
    ext n x
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  rcases m₁ with @⟨@⟨⟨_⟩⟩, ⟨_⟩⟩
  congr

@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@CommMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
theorem CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul

@[to_additive]
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul

@[to_additive]
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul

@[to_additive]
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
theorem CancelMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul

@[to_additive]
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  grind

@[to_additive (attr := ext)]
theorem CancelCommMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelCommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul

@[to_additive (attr := ext)]
theorem DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M))
    (h_inv : (letI := m₁; Inv.inv : M → M) = (letI := m₂; Inv.inv : M → M)) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMul m₁.toOne m₂.toMul m₂.toOne :=
    @MonoidHom.mk M M m₁.toMul m₁.toOne m₂.toMul m₂.toOne
      (@OneHom.mk _ _ m₁.toOne m₂.toOne id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext a b
    exact @map_div' _ _
      (F := @MonoidHom _ _ m₁.toMul m₁.toOne m₂.toMul m₂.toOne) _
      (id _) _ inferInstance f (congr_fun h_inv) a b
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  congr

@[to_additive]
lemma Group.toDivInvMonoid_injective {G : Type*} : Injective (@Group.toDivInvMonoid G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
theorem Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) :
    g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMul g₁.toOne g₂.toMul g₂.toOne :=
    @MonoidHom.mk G G g₁.toMul g₁.toOne g₂.toMul g₂.toOne
      (@OneHom.mk _ _ g₁.toOne g₂.toOne id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ g₂.toDivisionMonoid f))

@[to_additive]
lemma CommGroup.toGroup_injective {G : Type*} : Injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
theorem CommGroup.ext {G : Type*} ⦃g₁ g₂ : CommGroup G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
