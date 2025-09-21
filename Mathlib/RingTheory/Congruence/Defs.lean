/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.Tactic.FastInstance

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
* Copy across more API from `Con` and `AddCon` in `GroupTheory/Congruence.lean`.
-/


/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where

/-- The induced multiplicative congruence from a `RingCon`. -/
add_decl_doc RingCon.toCon

/-- The induced additive congruence from a `RingCon`. -/
add_decl_doc RingCon.toAddCon

variable {R : Type*}

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

/-- The inductively defined smallest ring congruence relation containing a given binary
relation. -/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : FunLike (RingCon R) R (R → Prop) where
  coe c := c.r
  coe_injective' x y h := by
    rcases x with ⟨⟨x, _⟩, _⟩
    rcases y with ⟨⟨y, _⟩, _⟩
    congr!
    rw [Setoid.ext_iff, (show ⇑x = ⇑y from h)]
    simp

@[simp]
theorem coe_mk (s : Con R) (h) : ⇑(mk s h) = s := rfl

theorem rel_eq_coe : c.r = c :=
  rfl

@[simp]
theorem toCon_coe_eq_coe : (c.toCon : R → R → Prop) = c :=
  rfl

protected theorem refl (x) : c x x :=
  c.refl' x

protected theorem symm {x y} : c x y → c y x :=
  c.symm'

protected theorem trans {x y z} : c x y → c y z → c x z :=
  c.trans'

protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
  c.add'

protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
  c.mul'

protected theorem sub {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    {a b c d : S} (h : t a b) (h' : t c d) : t (a - c) (b - d) := t.toAddCon.sub h h'

protected theorem neg {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    {a b} (h : t a b) : t (-a) (-b) := t.toAddCon.neg h

protected theorem nsmul {S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
    (m : ℕ) {x y : S} (hx : t x y) : t (m • x) (m • y) := t.toAddCon.nsmul m hx

protected theorem zsmul {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    (z : ℤ) {x y : S} (hx : t x y) : t (z • x) (z • y) := t.toAddCon.zsmul z hx

instance : Inhabited (RingCon R) :=
  ⟨ringConGen EmptyRelation⟩

@[simp]
theorem rel_mk {s : Con R} {h a b} : RingCon.mk s h a b ↔ s a b :=
  Iff.rfl

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
theorem ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
@[ext]
theorem ext {c d : RingCon R} (H : ∀ x y, c x y ↔ d x y) : c = d :=
  ext' <| by ext; apply H

/--
Pulling back a `RingCon` across a ring homomorphism.
-/
def comap {R R' F : Type*} [Add R] [Add R']
    [FunLike F R R'] [AddHomClass F R R'] [Mul R] [Mul R'] [MulHomClass F R R']
    (J : RingCon R') (f : F) :
    RingCon R where
  __ := J.toCon.comap f (map_mul f)
  __ := J.toAddCon.comap f (map_add f)

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def Quotient :=
  Quotient c.toSetoid

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

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
protected theorem eq {a b : R} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''

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

instance : Mul c.Quotient := inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

instance : Zero c.Quotient := inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

instance : One c.Quotient := inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl

end One

section NegSubZSMul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance : Neg c.Quotient := inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl

instance : Sub c.Quotient := inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl

instance hasZSMul : SMul ℤ c.Quotient := inferInstanceAs (SMul ℤ c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • (x : c.Quotient) :=
  rfl

end NegSubZSMul

section NSMul

variable [AddMonoid R] [Mul R] (c : RingCon R)

instance hasNSMul : SMul ℕ c.Quotient := inferInstanceAs (SMul ℕ c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • (x : c.Quotient) :=
  rfl

end NSMul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient ℕ := inferInstanceAs (Pow c.toCon.Quotient ℕ)

@[simp, norm_cast]
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n :=
  rfl

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]
theorem coe_intCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl

end IntCast

instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : RingCon R` preserve the algebraic structure of `R`.
-/


section Algebraic

instance [NonUnitalNonAssocSemiring R] (c : RingCon R) :
    NonUnitalNonAssocSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient := fast_instance%
  Function.Surjective.nonAssocSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Semiring R] (c : RingCon R) : Semiring c.Quotient := fast_instance%
  Function.Surjective.semiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient := fast_instance%
  Function.Surjective.commSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing R] (c : RingCon R) :
    NonUnitalNonAssocRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient := fast_instance%
  Function.Surjective.nonAssocRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Ring R] (c : RingCon R) : Ring c.Quotient := fast_instance%
  Function.Surjective.ring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient := fast_instance%
  Function.Surjective.commRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

end Algebraic

/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end Quotient

end RingCon
