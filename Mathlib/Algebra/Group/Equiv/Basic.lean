/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Multiplicative and additive equivs

This file contains basic results on `MulEquiv` and `AddEquiv`.

## Tags

Equiv, MulEquiv, AddEquiv
-/

assert_not_exists Fintype

open Function

variable {F α β M N P G H : Type*}

namespace EmbeddingLike
variable [One M] [One N] [FunLike F M N] [EmbeddingLike F M N] [OneHomClass F M N]

end EmbeddingLike

variable [EquivLike F α β]

@[to_additive]
theorem MulEquivClass.toMulEquiv_injective [Mul α] [Mul β] [MulEquivClass F α β] :
    Function.Injective ((↑) : F → α ≃* β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ congr_arg (fun e : α ≃* β ↦ e.toFun a) e

namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]

section unique

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive "The `AddEquiv` between two `AddMonoid`s with a unique element."]
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.ofUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }

@[to_additive (attr := deprecated ofUnique (since := "2024-12-25"))]
alias mulEquivOfUnique := ofUnique

/-- Alias of `AddEquiv.ofEquiv`. -/
add_decl_doc AddEquiv.addEquivOfUnique

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with
  a unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

end unique

end Mul

/-!
## Monoids
-/

/-- A multiplicative analogue of `Equiv.arrowCongr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive (attr := simps apply) "An additive analogue of `Equiv.arrowCongr`,
  where the equivalence between the targets is additive."]
def arrowCongr {M N P Q : Type*} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) :
    (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp

/-- A multiplicative analogue of `Equiv.arrowCongr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[to_additive (attr := simps apply)
  "An additive analogue of `Equiv.arrowCongr`,
  for additive maps from an additive monoid to a commutative additive monoid."]
def monoidHomCongr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q]
    (f : M ≃* N) (g : P ≃* Q) : (M →* P) ≃* (N →* Q) where
  toFun h := g.toMonoidHom.comp (h.comp f.symm.toMonoidHom)
  invFun k := g.symm.toMonoidHom.comp (k.comp f.toMonoidHom)
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `MulEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`MulEquiv.arrowCongr`.
-/
@[to_additive (attr := simps apply)
  "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`
  generates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.

  This is the `AddEquiv` version of `Equiv.piCongrRight`, and the dependent version of
  `AddEquiv.arrowCongr`."]
def piCongrRight {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equiv.piCongrRight fun j => (es j).toEquiv with
    toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j),
    map_mul' := fun x y => funext fun j => map_mul (es j) (x j) (y j) }

@[to_additive (attr := simp)]
theorem piCongrRight_refl {η : Type*} {Ms : η → Type*} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ := rfl

@[to_additive (attr := simp)]
theorem piCongrRight_symm {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = piCongrRight fun i => (es i).symm := rfl

@[to_additive (attr := simp)]
theorem piCongrRight_trans {η : Type*} {Ms Ns Ps : η → Type*} [∀ j, Mul (Ms j)]
    [∀ j, Mul (Ns j)] [∀ j, Mul (Ps j)] (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = piCongrRight fun i => (es i).trans (fs i) := rfl

/-- A family indexed by a type with a unique element
is `MulEquiv` to the element at the single index. -/
@[to_additive (attr := simps!)
  "A family indexed by a type with a unique element
  is `AddEquiv` to the element at the single index."]
def piUnique {ι : Type*} (M : ι → Type*) [∀ j, Mul (M j)] [Unique ι] :
    (∀ j, M j) ≃* M default :=
  { Equiv.piUnique M with map_mul' := fun _ _ => Pi.mul_apply _ _ _ }

end MulEquiv

namespace MonoidHom

/-- The equivalence `(β →* γ) ≃ (α →* γ)` obtained by precomposition with
a multiplicative equivalence `e : α ≃* β`. -/
@[to_additive (attr := simps)
"The equivalence `(β →+ γ) ≃ (α →+ γ)` obtained by precomposition with
an additive equivalence `e : α ≃+ β`."]
def precompEquiv {α β : Type*} [Monoid α] [Monoid β] (e : α ≃* β) (γ : Type*) [Monoid γ] :
    (β →* γ) ≃ (α →* γ) where
  toFun f := f.comp e
  invFun g := g.comp e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The equivalence `(γ →* α) ≃ (γ →* β)` obtained by postcomposition with
a multiplicative equivalence `e : α ≃* β`. -/
@[to_additive (attr := simps)
"The equivalence `(γ →+ α) ≃ (γ →+ β)` obtained by postcomposition with
an additive equivalence `e : α ≃+ β`."]
def postcompEquiv {α β : Type*} [Monoid α] [Monoid β] (e : α ≃* β) (γ : Type*) [Monoid γ] :
    (γ →* α) ≃ (γ →* β) where
  toFun f := e.toMonoidHom.comp f
  invFun g := e.symm.toMonoidHom.comp g
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

end MonoidHom

namespace Equiv

section InvolutiveInv

variable (G) [InvolutiveInv G]

/-- Inversion on a `Group` or `GroupWithZero` is a permutation of the underlying type. -/
@[to_additive (attr := simps! -fullyApplied apply)
    "Negation on an `AddGroup` is a permutation of the underlying type."]
protected def inv : Perm G :=
  inv_involutive.toPerm _

variable {G}

@[to_additive (attr := simp)]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G := rfl

end InvolutiveInv

end Equiv
