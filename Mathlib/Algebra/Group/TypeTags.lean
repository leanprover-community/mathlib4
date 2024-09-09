/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Nontrivial.Basic

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Order.Synonym`.

## Porting notes

- Since bundled morphism applications that rely on `CoeFun` currently don't work, they are ported
  as `toFoo a` rather than `a.toFoo` for now. (https://github.com/leanprover/lean4/issues/1910)

-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

universe u v

variable {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `Additive α` carries the corresponding
additive structure. -/
def Additive (α : Type*) := α

/-- If `α` carries some additive structure, then `Multiplicative α` carries the corresponding
multiplicative structure. -/
def Multiplicative (α : Type*) := α

namespace Additive

/-- Reinterpret `x : α` as an element of `Additive α`. -/
def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Additive α` as an element of `α`. -/
def toMul : Additive α ≃ α := ofMul.symm

@[simp]
theorem ofMul_symm_eq : (@ofMul α).symm = toMul :=
  rfl

@[simp]
theorem toMul_symm_eq : (@toMul α).symm = ofMul :=
  rfl

@[simp]
protected lemma «forall» {p : Additive α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofMul a) := Iff.rfl

@[simp]
protected lemma «exists» {p : Additive α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofMul a) := Iff.rfl

/-- Recursion principle for `Additive`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : Additive α → Sort*} (ofMul : ∀ a, motive (ofMul a)) : ∀ a, motive a :=
  fun a => ofMul (toMul a)

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `Multiplicative α`. -/
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Multiplicative α` as an element of `α`. -/
def toAdd : Multiplicative α ≃ α := ofAdd.symm

@[simp]
theorem ofAdd_symm_eq : (@ofAdd α).symm = toAdd :=
  rfl

@[simp]
theorem toAdd_symm_eq : (@toAdd α).symm = ofAdd :=
  rfl

@[simp]
protected lemma «forall» {p : Multiplicative α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofAdd a) := Iff.rfl

@[simp]
protected lemma «exists» {p : Multiplicative α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofAdd a) := Iff.rfl

/-- Recursion principle for `Multiplicative`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : Multiplicative α → Sort*} (ofAdd : ∀ a, motive (ofAdd a)) : ∀ a, motive a :=
  fun a => ofAdd (toAdd a)

end Multiplicative

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

@[simp]
theorem toAdd_ofAdd (x : α) : toAdd (ofAdd x) = x :=
  rfl

@[simp]
theorem ofAdd_toAdd (x : Multiplicative α) : ofAdd (toAdd x) = x :=
  rfl

@[simp]
theorem toMul_ofMul (x : α) : toMul (ofMul x) = x :=
  rfl

@[simp]
theorem ofMul_toMul (x : Additive α) : ofMul (toMul x) = x :=
  rfl

instance [Subsingleton α] : Subsingleton (Additive α) := toMul.injective.subsingleton
instance [Subsingleton α] : Subsingleton (Multiplicative α) := toAdd.injective.subsingleton

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩

instance [Unique α] : Unique (Additive α) := toMul.unique
instance [Unique α] : Unique (Multiplicative α) := toAdd.unique

instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)

instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)

instance [h : Infinite α] : Infinite (Additive α) := h

instance [h : Infinite α] : Infinite (Multiplicative α) := h

instance [h : DecidableEq α] : DecidableEq (Multiplicative α) := h

instance [h : DecidableEq α] : DecidableEq (Additive α) := h

instance Additive.instNontrivial [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul.injective.nontrivial

instance Multiplicative.instNontrivial [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd.injective.nontrivial

instance Additive.add [Mul α] : Add (Additive α) where
  add x y := ofMul (toMul x * toMul y)

instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (toAdd x + toAdd y)

@[simp]
theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y := rfl

@[simp]
theorem toAdd_mul [Add α] (x y : Multiplicative α) : toAdd (x * y) = toAdd x + toAdd y := rfl

@[simp]
theorem ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul y := rfl

@[simp]
theorem toMul_add [Mul α] (x y : Additive α) : toMul (x + y) = toMul x * toMul y := rfl

instance Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.add with add_assoc := @mul_assoc α _ }

instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with mul_assoc := @add_assoc α _ }

instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm α _ }

instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_comm α _ }

instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨@mul_left_cancel α _ _⟩

instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨@add_left_cancel α _ _⟩

instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨@mul_right_cancel α _ _⟩

instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨@add_right_cancel α _ _⟩

instance Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  ⟨⟩

instance Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  ⟨⟩

instance Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] :
    AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isLeftCancelAdd with }

instance Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] :
    LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

instance Additive.addRightCancelSemigroup [RightCancelSemigroup α] :
    AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isRightCancelAdd with }

instance Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] :
    RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl

@[simp]
theorem ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 := Iff.rfl

@[simp]
theorem toMul_zero [One α] : toMul (0 : Additive α) = 1 := rfl

@[simp]
lemma toMul_eq_one {α : Type*} [One α] {x : Additive α} :
    Additive.toMul x = 1 ↔ x = 0 :=
  Iff.rfl

instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

@[simp]
theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl

@[simp]
theorem toAdd_one [Zero α] : toAdd (1 : Multiplicative α) = 0 :=
  rfl

@[simp]
lemma toAdd_eq_zero {α : Type*} [Zero α] {x : Multiplicative α} :
    Multiplicative.toAdd x = 0 ↔ x = 1 :=
  Iff.rfl

instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero := 0
  add := (· + ·)
  zero_add := @one_mul α _
  add_zero := @mul_one α _

instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one := 1
  mul := (· * ·)
  one_mul := @zero_add α _
  mul_one := @add_zero α _

instance Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) :=
  { Additive.addZeroClass, Additive.addSemigroup with
    nsmul := @Monoid.npow α h
    nsmul_zero := @Monoid.npow_zero α h
    nsmul_succ := @Monoid.npow_succ α h }

instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) :=
  { Multiplicative.mulOneClass, Multiplicative.semigroup with
    npow := @AddMonoid.nsmul α h
    npow_zero := @AddMonoid.nsmul_zero α h
    npow_succ := @AddMonoid.nsmul_succ α h }

@[simp]
theorem ofMul_pow [Monoid α] (n : ℕ) (a : α) : ofMul (a ^ n) = n • ofMul a :=
  rfl

@[simp]
theorem toMul_nsmul [Monoid α] (n : ℕ) (a : Additive α) : toMul (n • a) = toMul a ^ n :=
  rfl

@[simp]
theorem ofAdd_nsmul [AddMonoid α] (n : ℕ) (a : α) : ofAdd (n • a) = ofAdd a ^ n :=
  rfl

@[simp]
theorem toAdd_pow [AddMonoid α] (a : Multiplicative α) (n : ℕ) : toAdd (a ^ n) = n • toAdd a :=
  rfl

instance Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with }

instance Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] :
    LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }

instance Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with }

instance Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] :
    RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }

instance Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with }

instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with }

instance Additive.neg [Inv α] : Neg (Additive α) :=
  ⟨fun x => ofAdd (toMul x)⁻¹⟩

@[simp]
theorem ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x :=
  rfl

@[simp]
theorem toMul_neg [Inv α] (x : Additive α) : toMul (-x) = (toMul x)⁻¹ :=
  rfl

instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofMul (-toAdd x)⟩

@[simp]
theorem ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹ :=
  rfl

@[simp]
theorem toAdd_inv [Neg α] (x : Multiplicative α) : toAdd x⁻¹ = -(toAdd x) :=
  rfl

instance Additive.sub [Div α] : Sub (Additive α) where
  sub x y := ofMul (toMul x / toMul y)

instance Multiplicative.div [Sub α] : Div (Multiplicative α) where
  div x y := ofAdd (toAdd x - toAdd y)

@[simp]
theorem ofAdd_sub [Sub α] (x y : α) : ofAdd (x - y) = ofAdd x / ofAdd y :=
  rfl

@[simp]
theorem toAdd_div [Sub α] (x y : Multiplicative α) : toAdd (x / y) = toAdd x - toAdd y :=
  rfl

@[simp]
theorem ofMul_div [Div α] (x y : α) : ofMul (x / y) = ofMul x - ofMul y :=
  rfl

@[simp]
theorem toMul_sub [Div α] (x y : Additive α) : toMul (x - y) = toMul x / toMul y :=
  rfl

instance Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.neg with neg_neg := @inv_inv α _ }

instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv := @neg_neg α _ }

instance Additive.subNegMonoid [DivInvMonoid α] : SubNegMonoid (Additive α) :=
  { Additive.neg, Additive.sub, Additive.addMonoid with
    sub_eq_add_neg := @div_eq_mul_inv α _
    zsmul := @DivInvMonoid.zpow α _
    zsmul_zero' := @DivInvMonoid.zpow_zero' α _
    zsmul_succ' := @DivInvMonoid.zpow_succ' α _
    zsmul_neg' := @DivInvMonoid.zpow_neg' α _ }

instance Multiplicative.divInvMonoid [SubNegMonoid α] : DivInvMonoid (Multiplicative α) :=
  { Multiplicative.inv, Multiplicative.div, Multiplicative.monoid with
    div_eq_mul_inv := @sub_eq_add_neg α _
    zpow := @SubNegMonoid.zsmul α _
    zpow_zero' := @SubNegMonoid.zsmul_zero' α _
    zpow_succ' := @SubNegMonoid.zsmul_succ' α _
    zpow_neg' := @SubNegMonoid.zsmul_neg' α _ }

@[simp]
theorem ofMul_zpow [DivInvMonoid α] (z : ℤ) (a : α) : ofMul (a ^ z) = z • ofMul a :=
  rfl

@[simp]
theorem toMul_zsmul [DivInvMonoid α] (z : ℤ) (a : Additive α) : toMul (z • a) = toMul a ^ z :=
  rfl

@[simp]
theorem ofAdd_zsmul [SubNegMonoid α] (z : ℤ) (a : α) : ofAdd (z • a) = ofAdd a ^ z :=
  rfl

@[simp]
theorem toAdd_zpow [SubNegMonoid α] (a : Multiplicative α) (z : ℤ) : toAdd (a ^ z) = z • toAdd a :=
  rfl

instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }

instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }

instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with neg_add_cancel := @inv_mul_cancel α _ }

instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with inv_mul_cancel := @neg_add_cancel α _ }

instance Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

instance Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

/-- Reinterpret `α →+ β` as `Multiplicative α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α →+ β) ≃ (Multiplicative α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (toAdd a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative [AddZeroClass α] [AddZeroClass β] (f : α →+ β) :
    ⇑(toMultiplicative f) = ofAdd ∘ f ∘ toAdd := rfl

/-- Reinterpret `α →* β` as `Additive α →+ Additive β`. -/
@[simps]
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃ (Additive α →+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f (toMul a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => toMul (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, norm_cast]
lemma MonoidHom.coe_toMultiplicative [MulOneClass α] [MulOneClass β] (f : α →* β) :
    ⇑(toAdditive f) = ofMul ∘ f ∘ toMul := rfl

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative' [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (toMul a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative' [MulOneClass α] [AddZeroClass β] (f : Additive α →+ β) :
    ⇑(toMultiplicative' f) = ofAdd ∘ f ∘ ofMul := rfl

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps!]
def MonoidHom.toAdditive' [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm

@[simp, norm_cast]
lemma MonoidHom.coe_toAdditive' [MulOneClass α] [AddZeroClass β] (f : α →* Multiplicative β) :
    ⇑(toAdditive' f) = toAdd ∘ f ∘ toMul := rfl

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicative'' [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun f := {
    toFun := fun a => toMul (f (toAdd a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative'' [AddZeroClass α] [MulOneClass β] (f : α →+ Additive β) :
    ⇑(toMultiplicative'' f) = toMul ∘ f ∘ toAdd := rfl

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps!]
def MonoidHom.toAdditive'' [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm

@[simp, norm_cast]
lemma MonoidHom.coe_toAdditive'' [AddZeroClass α] [MulOneClass β] (f : Multiplicative α →* β) :
    ⇑(toAdditive'' f) = ofMul ∘ f ∘ ofAdd := rfl

/-- If `α` has some multiplicative structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β (toMul a) :=
  ⟨fun a => CoeFun.coe (toMul a)⟩

/-- If `α` has some additive structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β (toAdd a) :=
  ⟨fun a => CoeFun.coe (toAdd a)⟩
