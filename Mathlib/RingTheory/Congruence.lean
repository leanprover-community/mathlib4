/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module ring_theory.congruence
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.Algebra.Hom.Ring
import Mathbin.Algebra.Ring.InjSurj
import Mathbin.GroupTheory.Congruence

/-!
# Congruence relations on rings

This file defines congruence relations on rings, which extend `con` and `add_con` on monoids and
additive monoids.

Most of the time you likely want to use the `ideal.quotient` API that is built on top of this.

## Main Definitions

* `ring_con R`: the type of congruence relations respecting `+` and `*`.
* `ring_con_gen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `ring_quot` too.
* Copy across more API from `con` and `add_con` in `group_theory/congruence.lean`, such as:
  * The `complete_lattice` structure.
  * The `con_gen_eq` lemma, stating that
    `ring_con_gen r = Inf {s : ring_con M | ∀ x y, r x y → s x y}`.
-/


/- Note: we can't extend both `add_con R` and `mul_con R` in Lean 3 due to interactions between old-
and new-style structures. We can revisit this in Lean 4. (After and not during the port!) -/
/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure RingCon (R : Type _) [Add R] [Mul R] extends Setoid R where
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)
#align ring_con RingCon

variable {α R : Type _}

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel x y
  | refl : ∀ x, RingConGen.Rel x x
  | symm : ∀ {x y}, RingConGen.Rel x y → RingConGen.Rel y x
  | trans : ∀ {x y z}, RingConGen.Rel x y → RingConGen.Rel y z → RingConGen.Rel x z
  | add : ∀ {w x y z}, RingConGen.Rel w x → RingConGen.Rel y z → RingConGen.Rel (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel w x → RingConGen.Rel y z → RingConGen.Rel (w * y) (x * z)
#align ring_con_gen.rel RingConGen.Rel

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R
    where
  R := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' _ _ _ _ := RingConGen.Rel.add
  mul' _ _ _ _ := RingConGen.Rel.mul
#align ring_con_gen ringConGen

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- Every `ring_con` is also an `add_con` -/
def toAddCon : AddCon R :=
  { c with }
#align ring_con.to_add_con RingCon.toAddCon

/-- Every `ring_con` is also a `con` -/
def toCon : Con R :=
  { c with }
#align ring_con.to_con RingCon.toCon

/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : CoeFun (RingCon R) fun _ => R → R → Prop :=
  ⟨fun c => c.R⟩

@[simp]
theorem rel_eq_coe : c.R = c :=
  rfl
#align ring_con.rel_eq_coe RingCon.rel_eq_coe

protected theorem refl (x) : c x x :=
  c.refl' x
#align ring_con.refl RingCon.refl

protected theorem symm {x y} : c x y → c y x :=
  c.symm'
#align ring_con.symm RingCon.symm

protected theorem trans {x y z} : c x y → c y z → c x z :=
  c.trans'
#align ring_con.trans RingCon.trans

protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
  c.add'
#align ring_con.add RingCon.add

protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
  c.mul'
#align ring_con.mul RingCon.mul

@[simp]
theorem rel_mk {s : Setoid R} {ha hm a b} : RingCon.mk s ha hm a b ↔ Setoid.r a b :=
  Iff.rfl
#align ring_con.rel_mk RingCon.rel_mk

instance : Inhabited (RingCon R) :=
  ⟨ringConGen EmptyRelation⟩

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def Quotient :=
  Quotient c.toSetoid
#align ring_con.quotient RingCon.Quotient

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : CoeTC R c.Quotient :=
  ⟨@Quotient.mk'' _ c.toSetoid⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  @Quotient.decidableEq R c.toSetoid d

@[simp]
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align ring_con.quot_mk_eq_coe RingCon.quot_mk_eq_coe

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
protected theorem eq {a b : R} : (a : c.Quotient) = b ↔ c a b :=
  Quotient.eq'
#align ring_con.eq RingCon.eq

end Basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/


section Data

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

instance : Add c.Quotient :=
  c.toAddCon.HasAdd

@[simp, norm_cast]
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl
#align ring_con.coe_add RingCon.coe_add

instance : Mul c.Quotient :=
  c.toCon.HasMul

@[simp, norm_cast]
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl
#align ring_con.coe_mul RingCon.coe_mul

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

instance : Zero c.Quotient :=
  c.toAddCon

@[simp, norm_cast]
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl
#align ring_con.coe_zero RingCon.coe_zero

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

instance : One c.Quotient :=
  c.toCon

@[simp, norm_cast]
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl
#align ring_con.coe_one RingCon.coe_one

end One

section Smul

variable [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] (c : RingCon R)

instance : SMul α c.Quotient :=
  c.toCon.HasSmul

@[simp, norm_cast]
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • x :=
  rfl
#align ring_con.coe_smul RingCon.coe_smul

end Smul

section NegSubZsmul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance : Neg c.Quotient :=
  c.toAddCon

@[simp, norm_cast]
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl
#align ring_con.coe_neg RingCon.coe_neg

instance : Sub c.Quotient :=
  c.toAddCon

@[simp, norm_cast]
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl
#align ring_con.coe_sub RingCon.coe_sub

instance hasZsmul : SMul ℤ c.Quotient :=
  c.toAddCon
#align ring_con.has_zsmul RingCon.hasZsmul

@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • x :=
  rfl
#align ring_con.coe_zsmul RingCon.coe_zsmul

end NegSubZsmul

section Nsmul

variable [AddMonoid R] [Mul R] (c : RingCon R)

instance hasNsmul : SMul ℕ c.Quotient :=
  c.toAddCon
#align ring_con.has_nsmul RingCon.hasNsmul

@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • x :=
  rfl
#align ring_con.coe_nsmul RingCon.coe_nsmul

end Nsmul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient ℕ :=
  c.toCon

@[simp, norm_cast]
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = x ^ n :=
  rfl
#align ring_con.coe_pow RingCon.coe_pow

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_nat_cast RingCon.coe_nat_cast

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]
theorem coe_int_cast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_int_cast RingCon.coe_int_cast

end IntCast

instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : ring_con R` preseverse the algebraic structure of `R`.
-/


section Algebraic

instance [NonUnitalNonAssocSemiring R] (c : RingCon R) : NonUnitalNonAssocSemiring c.Quotient :=
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient :=
  Function.Surjective.nonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient :=
  Function.Surjective.nonUnitalSemiring _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Semiring R] (c : RingCon R) : Semiring c.Quotient :=
  Function.Surjective.semiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient :=
  Function.Surjective.commSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing R] (c : RingCon R) : NonUnitalNonAssocRing c.Quotient :=
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient :=
  Function.Surjective.nonAssocRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient :=
  Function.Surjective.nonUnitalRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Ring R] (c : RingCon R) : Ring c.Quotient :=
  Function.Surjective.ring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  Function.Surjective.commRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient :=
  { c.toCon.MulAction with
    smul := (· • ·)
    smul_zero := fun r => congr_arg Quotient.mk' <| smul_zero _
    smul_add := fun r => Quotient.ind₂' fun m₁ m₂ => congr_arg Quotient.mk' <| smul_add _ _ _ }

instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient :=
  { c, c.toCon.MulDistribMulAction with smul := (· • ·) }

end Algebraic

/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient
    where
  toFun := Quotient.mk'
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align ring_con.mk' RingCon.mk'

end Quotient

end RingCon

