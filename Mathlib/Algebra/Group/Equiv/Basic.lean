/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Spread

/-!
# Multiplicative and additive equivs

This file contains basic results on `MulEquiv` and `AddEquiv`.

## Tags

Equiv, MulEquiv, AddEquiv
-/

@[expose] public section

assert_not_exists Fintype

open Function

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

@[to_additive]
theorem MulEquivClass.toMulEquiv_injective [Mul α] [Mul β] [MulEquivClass F α β] :
    Function.Injective ((↑) : F → α ≃* β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ congr_arg (fun e : α ≃* β ↦ e.toFun a) e

@[to_additive] theorem MulEquivClass.isDedekindFiniteMonoid_iff [MulOne α] [MulOne β]
    [MulEquivClass F α β] [OneHomClass F α β] (f : F) :
    IsDedekindFiniteMonoid α ↔ IsDedekindFiniteMonoid β where
  mp _ := let e := MulEquivClass.toMulEquiv f
    let g : β →* α := ⟨⟨e.symm, e.injective <| (e.right_inv ..).trans (map_one f).symm⟩, map_mul _⟩
    .of_injective g e.symm.injective
  mpr _ := let g : α →* β := ⟨⟨f, map_one f⟩, map_mul f⟩
    .of_injective g (EquivLike.injective f)

namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive /-- The `AddEquiv` between two `AddMonoid`s with a unique element. -/]
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.ofUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive /-- There is a unique additive monoid homomorphism between two additive monoids with
a unique element. -/]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

variable (α M) in
/-- If `α` has a unique term, then the product of magmas `α → M` is isomorphic to `M`. -/
@[to_additive (attr := simps!)
/-- If `α` has a unique term, then the product of magmas `α → M` is isomorphic to `M`. -/]
def funUnique [Unique α] : (α → M) ≃* M where
  toEquiv := .funUnique ..
  map_mul' := by simp

end Mul

/-!
## Monoids
-/

/-- A multiplicative analogue of `Equiv.arrowCongr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive (attr := simps apply) /-- An additive analogue of `Equiv.arrowCongr`,
where the equivalence between the targets is additive. -/]
def arrowCongr {M N P Q : Type*} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) :
    (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp

section monoidHomCongrEquiv
variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

/-- The equivalence `(M₁ →* N) ≃ (M₂ →* N)` obtained by postcomposition with
a multiplicative equivalence `e : M₁ ≃* M₂`. -/
@[to_additive (attr := simps)
/-- The equivalence `(M₁ →+ N) ≃ (M₂ →+ N)` obtained by postcomposition with
an additive equivalence `e : M₁ ≃+ M₂`. -/]
def monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) : (M₁ →* N) ≃ (M₂ →* N) where
  toFun f := f.comp e.symm.toMonoidHom
  invFun f := f.comp e.toMonoidHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-- The equivalence `(M →* N₁) ≃ (M →* N₂)` obtained by postcomposition with
a multiplicative equivalence `e : N₁ ≃* N₂`. -/
@[to_additive (attr := simps)
/-- The equivalence `(M →+ N₁) ≃ (M →+ N₂)` obtained by postcomposition with
an additive equivalence `e : N₁ ≃+ N₂`. -/]
def monoidHomCongrRightEquiv (e : N₁ ≃* N₂) : (M →* N₁) ≃ (M →* N₂) where
  toFun := e.toMonoidHom.comp
  invFun := e.symm.toMonoidHom.comp
  left_inv f := by ext; simp
  right_inv f := by ext; simp

@[to_additive (attr := simp)]
lemma monoidHomCongrLeftEquiv_refl : monoidHomCongrLeftEquiv (.refl M) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
lemma monoidHomCongrRightEquiv_refl : monoidHomCongrRightEquiv (.refl N) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
lemma symm_monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) :
    (monoidHomCongrLeftEquiv e).symm = monoidHomCongrLeftEquiv (N := N) e.symm := rfl

@[to_additive (attr := simp)]
lemma symm_monoidHomCongrRightEquiv (e : N₁ ≃* N₂) :
    (monoidHomCongrRightEquiv e).symm = monoidHomCongrRightEquiv (M := M) e.symm := rfl

@[to_additive (attr := simp)]
lemma monoidHomCongrLeftEquiv_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    monoidHomCongrLeftEquiv (N := N) (e₁₂.trans e₂₃) =
      (monoidHomCongrLeftEquiv e₁₂).trans (monoidHomCongrLeftEquiv e₂₃) := rfl

@[to_additive (attr := simp)]
lemma monoidHomCongrRightEquiv_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    monoidHomCongrRightEquiv (M := M) (e₁₂.trans e₂₃) =
      (monoidHomCongrRightEquiv e₁₂).trans (monoidHomCongrRightEquiv e₂₃) := rfl

end monoidHomCongrEquiv

section monoidHomCongr
variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

/-- The isomorphism `(M₁ →* N) ≃* (M₂ →* N)` obtained by postcomposition with
a multiplicative equivalence `e : M₁ ≃* M₂`. -/
@[to_additive (attr := simps! apply)
/-- The isomorphism `(M₁ →+ N) ≃+ (M₂ →+ N)` obtained by postcomposition with
an additive equivalence `e : M₁ ≃+ M₂`. -/]
def monoidHomCongrLeft (e : M₁ ≃* M₂) : (M₁ →* N) ≃* (M₂ →* N) where
  __ := e.monoidHomCongrLeftEquiv
  map_mul' f g := by ext; simp

/-- The isomorphism `(M →* N₁) ≃* (M →* N₂)` obtained by postcomposition with
a multiplicative equivalence `e : N₁ ≃* N₂`. -/
@[to_additive (attr := simps! apply)
/-- The isomorphism `(M →+ N₁) ≃+ (M →+ N₂)` obtained by postcomposition with
an additive equivalence `e : N₁ ≃+ N₂`. -/]
def monoidHomCongrRight (e : N₁ ≃* N₂) : (M →* N₁) ≃* (M →* N₂) where
  __ := e.monoidHomCongrRightEquiv
  map_mul' f g := by ext; simp

@[to_additive (attr := simp)]
lemma monoidHomCongrLeft_refl : monoidHomCongrLeft (.refl M) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
lemma monoidHomCongrRight_refl : monoidHomCongrRight (.refl N) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
lemma symm_monoidHomCongrLeft (e : M₁ ≃* M₂) :
    (monoidHomCongrLeft e).symm = monoidHomCongrLeft (N := N) e.symm := rfl

@[to_additive (attr := simp)]
lemma symm_monoidHomCongrRight (e : N₁ ≃* N₂) :
    (monoidHomCongrRight e).symm = monoidHomCongrRight (M := M) e.symm := rfl

@[to_additive (attr := simp)]
lemma monoidHomCongrLeft_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    monoidHomCongrLeft (N := N) (e₁₂.trans e₂₃) =
      (monoidHomCongrLeft e₁₂).trans (monoidHomCongrLeft e₂₃) := rfl

@[to_additive (attr := simp)]
lemma monoidHomCongrRight_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    monoidHomCongrRight (M := M) (e₁₂.trans e₂₃) =
      (monoidHomCongrRight e₁₂).trans (monoidHomCongrRight e₂₃) := rfl

end monoidHomCongr

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `MulEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`MulEquiv.arrowCongr`.
-/
@[to_additive (attr := simps apply)
  /-- A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`
  generates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.

  This is the `AddEquiv` version of `Equiv.piCongrRight`, and the dependent version of
  `AddEquiv.arrowCongr`. -/]
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
  /-- A family indexed by a type with a unique element
  is `AddEquiv` to the element at the single index. -/]
def piUnique {ι : Type*} (M : ι → Type*) [∀ j, Mul (M j)] [Unique ι] :
    (∀ j, M j) ≃* M default :=
  { Equiv.piUnique M with map_mul' := fun _ _ => Pi.mul_apply _ _ _ }

end MulEquiv

namespace Equiv

section InvolutiveInv

variable (G) [InvolutiveInv G]

/-- Inversion on a `Group` or `GroupWithZero` is a permutation of the underlying type. -/
@[to_additive (attr := simps! -fullyApplied apply)
    /-- Negation on an `AddGroup` is a permutation of the underlying type. -/]
protected def inv : Perm G :=
  inv_involutive.toPerm _

variable {G}

@[to_additive (attr := simp)]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G := rfl

end InvolutiveInv

end Equiv
