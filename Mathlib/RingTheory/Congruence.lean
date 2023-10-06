/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.Algebra.Hom.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.GroupTheory.Congruence

#align_import ring_theory.congruence from "leanprover-community/mathlib"@"2f39bcbc98f8255490f8d4562762c9467694c809"

/-!
# Congruence relations on rings

This file defines congruence relations on rings, which extend `Con` and `AddCon` on monoids and
additive monoids.

Most of the time you likely want to use the `Ideal.Quotient` API that is built on top of this.

## Main Definitions

* `RingCon R`: the type of congruence relations respecting `+` and `*`.
* `RingConGen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `RingQuot` too.
* Copy across more API from `Con` and `AddCon` in `GroupTheory/Congruence.lean`, such as:
  * The `CompleteLattice` structure.
  * The `conGen_eq` lemma, stating that
    `ringConGen r = sInf {s : RingCon M | ∀ x y, r x y → s x y}`.
-/


/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where
#align ring_con RingCon

/-- The induced multiplicative congruence from a `RingCon`. -/
add_decl_doc RingCon.toCon

/-- The induced additive congruence from a `RingCon`. -/
add_decl_doc RingCon.toAddCon

variable {α R : Type*}

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel r x y
  | refl : ∀ x, RingConGen.Rel r x x
  | symm : ∀ {x y}, RingConGen.Rel r x y → RingConGen.Rel r y x
  | trans : ∀ {x y z}, RingConGen.Rel r x y → RingConGen.Rel r y z → RingConGen.Rel r x z
  | add : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w * y) (x * z)
#align ring_con_gen.rel RingConGen.Rel

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul
#align ring_con_gen ringConGen

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

--Porting note: upgrade to `FunLike`
/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : FunLike (RingCon R) R fun _ => R → Prop :=
  { coe := fun c => c.r,
    coe_injective' := fun x y h => by
      rcases x with ⟨⟨x, _⟩, _⟩
      rcases y with ⟨⟨y, _⟩, _⟩
      congr!
      rw [Setoid.ext_iff,(show x.Rel = y.Rel from h)]
      simp}

theorem rel_eq_coe : c.r = c :=
  rfl
#align ring_con.rel_eq_coe RingCon.rel_eq_coe

@[simp]
theorem toCon_coe_eq_coe : (c.toCon : R → R → Prop) = c :=
  rfl

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

instance : Inhabited (RingCon R) :=
  ⟨ringConGen EmptyRelation⟩

@[simp]
theorem rel_mk {s : Con R} {h a b} : RingCon.mk s h a b ↔ @Setoid.r _ s.toSetoid a b :=
  Iff.rfl

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def Quotient :=
  Quotient c.toSetoid
#align ring_con.quotient RingCon.Quotient

variable {c}

/-- The morphism into the quotient by a congruence relation -/
@[coe] def toQuotient (r : R) : c.Quotient :=
  @Quotient.mk'' _ c.toSetoid r

variable (c)

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : CoeTC R c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [_d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[simp]
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align ring_con.quot_mk_eq_coe RingCon.quot_mk_eq_coe

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
protected theorem eq {a b : R} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''
#align ring_con.eq RingCon.eq

end Basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/


section Data

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

instance : Add c.Quotient := inferInstanceAs (Add c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl
#align ring_con.coe_add RingCon.coe_add

instance : Mul c.Quotient := inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl
#align ring_con.coe_mul RingCon.coe_mul

end add_mul

section Zero

variable [Zero R] [Add R] [Mul R] (c : RingCon R)

instance zero : Zero c.Quotient := inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : c.Quotient) = 0 :=
  rfl
#align ring_con.coe_zero RingCon.coe_zero

end Zero

section One

variable [One R] [Add R] [Mul R] (c : RingCon R)

instance one : One c.Quotient := inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_one : ((1 : R) : c.Quotient) = 1 :=
  rfl
#align ring_con.coe_one RingCon.coe_one

end One

section SMul

variable [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] (c : RingCon R)

instance smul : SMul α c.Quotient := inferInstanceAs (SMul α c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl
#align ring_con.coe_smul RingCon.coe_smul

end SMul

section NegSubZsmul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance neg : Neg c.Quotient := inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl
#align ring_con.coe_neg RingCon.coe_neg

instance sub : Sub c.Quotient := inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl
#align ring_con.coe_sub RingCon.coe_sub

instance zsmul : SMul ℤ c.Quotient := inferInstanceAs (SMul ℤ c.toAddCon.Quotient)
#align ring_con.has_zsmul RingCon.zsmul

@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • (x : c.Quotient) :=
  rfl
#align ring_con.coe_zsmul RingCon.coe_zsmul

end NegSubZsmul

section Nsmul

variable [AddMonoid R] [Mul R] (c : RingCon R)

instance nsmul : SMul ℕ c.Quotient := inferInstanceAs (SMul ℕ c.toAddCon.Quotient)
#align ring_con.has_nsmul RingCon.nsmul

@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • (x : c.Quotient) :=
  rfl
#align ring_con.coe_nsmul RingCon.coe_nsmul

end Nsmul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient ℕ := inferInstanceAs (Pow c.toCon.Quotient ℕ)

@[simp, norm_cast]
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n :=
  rfl
#align ring_con.coe_pow RingCon.coe_pow

end Pow

section NatCast

variable [NatCast R] [Add R] [Mul R] (c : RingCon R)

instance natCast : NatCast c.Quotient :=
  ⟨fun n => (n : R)⟩

theorem natCast_eq (n : ℕ) : (RingCon.natCast c).natCast n = ((n : R) : c.Quotient) := rfl

@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : ((n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_nat_cast RingCon.coe_nat_cast

end NatCast

section IntCast

variable [IntCast R] [Add R] [Mul R] (c : RingCon R)

instance intCast : IntCast c.Quotient :=
  ⟨fun z => (z : R)⟩

theorem intCast_eq (n : ℤ) : (RingCon.intCast c).intCast n = ((n : R) : c.Quotient) := rfl

@[simp, norm_cast]
theorem coe_int_cast (n : ℕ) : ((n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_int_cast RingCon.coe_int_cast

end IntCast

instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : RingCon R` preserve the algebraic structure of `R`.
-/


section Algebraic

instance mulZeroClass [Add R] [MulZeroClass R] (c : RingCon R) : MulZeroClass c.Quotient :=
  { zero_mul := Quotient.ind' fun _ => congrArg _ <| zero_mul _
    mul_zero := Quotient.ind' fun _ => congrArg _ <| mul_zero _ }

instance mulZeroOneClass [Add R] [MulZeroOneClass R] (c : RingCon R) :
    MulZeroOneClass c.Quotient :=
  { RingCon.mulZeroClass c, Con.mulOneClass c.toCon with }

instance addMonoidWithOne [AddMonoidWithOne R] [Mul R] (c : RingCon R) :
    AddMonoidWithOne c.Quotient :=
  { natCast _, AddCon.addMonoid c.toAddCon, one c with
    natCast_zero := congrArg _ <| AddMonoidWithOne.natCast_zero
    natCast_succ := fun _ => congrArg _ <| AddMonoidWithOne.natCast_succ _ }

instance addGroupWithOne [AddCommGroupWithOne R] [Mul R] (c : RingCon R) :
    AddGroupWithOne c.Quotient :=
  { intCast _, RingCon.addMonoidWithOne _, AddCon.addGroup c.toAddCon with
    intCast_ofNat := fun _ => congrArg _ <| AddGroupWithOne.intCast_ofNat _
    intCast_negSucc := fun _ => congrArg _ <| AddGroupWithOne.intCast_negSucc _ }

instance distrib [Distrib R] (c : RingCon R) : Distrib c.Quotient :=
  { left_distrib := fun a b c => Quotient.inductionOn₃' a b c
      fun _ _ _ => congrArg Quotient.mk'' <| left_distrib ..
    right_distrib := fun a b c => Quotient.inductionOn₃' a b c
      fun _ _ _ => congrArg Quotient.mk'' <| right_distrib .. }

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (c : RingCon R) :
    NonUnitalNonAssocSemiring c.Quotient :=
  { AddCon.addCommMonoid c.toAddCon, RingCon.mulZeroClass c, RingCon.distrib c with }

instance nonAssocSemiring [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient :=
  { RingCon.nonUnitalNonAssocSemiring c, RingCon.addMonoidWithOne c,
      RingCon.mulZeroOneClass c with }

instance nonUnitalSemiring [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient :=
  { mul_assoc := fun x y z => Quotient.inductionOn₃' x y z fun _ _ _ =>
      congrArg Quotient.mk'' <| mul_assoc .. }

instance semiring [Semiring R] (c : RingCon R) : Semiring c.Quotient :=
  { RingCon.nonUnitalSemiring c, RingCon.nonAssocSemiring c with }

instance commSemiring [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient :=
  { mul_comm := Quotient.ind₂' fun _ _ => congrArg Quotient.mk'' <| mul_comm .. }

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (c : RingCon R) :
    NonUnitalNonAssocRing c.Quotient :=
  { RingCon.nonUnitalNonAssocSemiring c, AddCon.addGroup c.toAddCon with }

instance nonAssocRing [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient :=
  { RingCon.nonUnitalNonAssocRing c, RingCon.addGroupWithOne c, RingCon.mulZeroOneClass c with }

instance nonUnitalRing [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient :=
  { RingCon.nonUnitalNonAssocRing c, RingCon.nonUnitalSemiring c with }

instance ring [Ring R] (c : RingCon R) : Ring c.Quotient :=
  { RingCon.nonAssocRing c, RingCon.nonUnitalRing c with }

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  { mul_comm := mul_comm }

instance isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient where
  smul_assoc _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul_assoc ..
#align ring_con.is_scalar_tower_right RingCon.isScalarTower_right

instance smulCommClass [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : RingCon R) : SMulCommClass α c.Quotient c.Quotient where
  smul_comm _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| (mul_smul_comm ..).symm
#align ring_con.smul_comm_class RingCon.smulCommClass

instance smulCommClass' [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass R α R] (c : RingCon R) : SMulCommClass c.Quotient α c.Quotient :=
  haveI := SMulCommClass.symm R α R
  SMulCommClass.symm ..
#align ring_con.smul_comm_class' RingCon.smulCommClass'

instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient :=
  { c.toCon.mulAction with
    smul_zero := fun _ => congr_arg toQuotient <| smul_zero _
    smul_add := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient <| smul_add .. }

instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient :=
  { smul_one := fun _ => congr_arg toQuotient <| smul_one _
    smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient <|
      MulSemiringAction.smul_mul .. }

end Algebraic

/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient
    where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align ring_con.mk' RingCon.mk'

end Quotient

end RingCon
