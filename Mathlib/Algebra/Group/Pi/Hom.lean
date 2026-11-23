/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Util.Delaborators

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Extra definitions about products of monoids and groups

This file defines various operations on products as bundled homomorphisms.
-/

@[expose] public section

assert_not_exists AddMonoidWithOne MonoidWithZero

variable {ι α I : Type*}
variable {f : I → Type*} {M N : ι → Type*}

section MulHom

variable [(i : I) → Mul (f i)]

/-- A family of MulHom's `f a : γ →ₙ* β a` defines a MulHom `MulHom.pi f : γ →ₙ* Π a, β a`
given by `MulHom.pi f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of AddHom's `f a : γ → β a` defines an AddHom `AddHom.pi f : γ → Π a, β a` given by
  `AddHom.pi f x b = f b x`. -/]
def MulHom.pi {γ : Type*} [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom := MulHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom_apply := MulHom.pi_apply

@[to_additive]
theorem MulHom.pi_injective {γ : Type*} [Nonempty I] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (MulHom.pi g) := fun _ _ h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((funext_iff.mp h :) i)

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MulHom.injective_pi := MulHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.mulHom_injective := MulHom.pi_injective

variable (f)

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `Function.eval i` as a `MulHom`. -/
@[to_additive (attr := simps)
  /-- Evaluation of functions into an indexed collection of additive semigroups at a point is an
  additive semigroup homomorphism. This is `Function.eval i` as an `AddHom`. -/]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i

/-- A family of MulHom's `f i : M i →ₙ* N i` defines a MulHom
`MulHom.piMap f : (Π i, M i) →ₙ* (Π i, N i)`
given by `MulHom.piMap f x i = f i x`. This is `Pi.map` for `MulHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of AddHom's `f i : M i →ₙ+ N i` defines an AddHom
  `AddHom.piMap f : (Π i, M i) →ₙ+ (Π i, N i)`
  given by `AddHom.piMap f x i = f i x`. This is `Pi.map` for `AddHom`s. -/]
def MulHom.piMap [Π i, Mul (M i)] [Π i, Mul (N i)] (g : Π i, M i →ₙ* N i) :
    (Π i, M i) →ₙ* (Π i, N i) :=
  .pi fun i ↦ (g i).comp (Pi.evalMulHom M i)

/-- `Function.const` as a `MulHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddHom`. -/]
def Pi.constMulHom (α β : Type*) [Mul β] :
    β →ₙ* α → β where
  toFun := Function.const α
  map_mul' _ _ := rfl

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps) /-- Additive semigroup homomorphism between the function spaces
  `I → α` and `I → β`, induced by an additive semigroup homomorphism `f` between `α` and `β` -/]
protected def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type*) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp

end MulHom

section MonoidHom

variable [(i : I) → MulOneClass (f i)]

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`Pi.monoidHom f : γ →* Π a, β a` given by `Pi.monoidHom f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid homomorphism
  `Pi.addMonoidHom f : γ →+ Π a, β a` given by `Pi.addMonoidHom f x b = f b x`. -/]
def MonoidHom.pi {γ : Type*} [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { MulHom.pi fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.monoidHom := MonoidHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_apply := MonoidHom.pi_apply

@[to_additive]
theorem MonoidHom.pi_injective {γ : Type*} [Nonempty I] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (MonoidHom.pi g) :=
  MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MonoidHom.injective_pi := MonoidHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_injective := MonoidHom.pi_injective

variable (f)

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `Function.eval i` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- Evaluation of functions into an indexed collection of additive
monoids at a point is an additive monoid homomorphism. This is `Function.eval i` as an
`AddMonoidHom`. -/]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[simp, norm_cast]
lemma Pi.coe_evalMonoidHom (i : I) : ⇑(evalMonoidHom f i) = Function.eval i := rfl

/-- A family of monoid homomorphisms `f i : M i →* N i` defines a monoid homomorphism
`MonoidHom.piMap f : (Π i, M i) →* (Π i, N i)`
given by `MonoidHom.piMap f x i = f i x`. This is `Pi.map` for `MonoidHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of additive monoid homomorphisms `f i : M i →+ N i` defines an additive monoid
  homomorphism  `AddMonoidHom.piMap f : (Π i, M i) →+ (Π i, N i)`
  given by `AddMonoidHom.piMap f x i = f i x`. This is `Pi.map` for `AddMonoidHom`s. -/]
def MonoidHom.piMap [Π i, MulOneClass (M i)] [Π i, MulOneClass (N i)] (g : Π i, M i →* N i) :
    (Π i, M i) →* (Π i, N i) :=
  .pi fun i ↦ (g i).comp (Pi.evalMonoidHom M i)

/-- `Function.const` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddMonoidHom`. -/]
def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps)
  /-- Additive monoid homomorphism between the function spaces `I → α` and `I → β`, induced by an
  additive monoid homomorphism `f` between `α` and `β` -/]
protected def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type*) : (I → α) →* I → β where
  toFun h := f ∘ h
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end MonoidHom
