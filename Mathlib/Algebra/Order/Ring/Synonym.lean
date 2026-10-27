/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Ring.Defs

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

public section


variable {R : Type*}

/-! ### Order dual -/

namespace OrderDual

instance [Distrib R] : Distrib Rᵒᵈ := inferInstanceAs <| Distrib R

instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ :=
  inferInstanceAs <| LeftDistribClass R

instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ :=
  inferInstanceAs <| RightDistribClass R

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ :=
  inferInstanceAs <| NonUnitalNonAssocSemiring R

instance [NatCast R] : NatCast Rᵒᵈ := inferInstanceAs <| NatCast R

instance [IntCast R] : IntCast Rᵒᵈ := inferInstanceAs <| IntCast R

instance [AddMonoidWithOne R] : AddMonoidWithOne Rᵒᵈ := inferInstanceAs <| AddMonoidWithOne R

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵒᵈ :=
  inferInstanceAs <| AddCommMonoidWithOne R

instance [AddGroupWithOne R] : AddGroupWithOne Rᵒᵈ := inferInstanceAs <| AddGroupWithOne R

instance [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵒᵈ :=
  inferInstanceAs <| AddCommGroupWithOne R

instance [NonUnitalSemiring R] : NonUnitalSemiring Rᵒᵈ := inferInstanceAs <| NonUnitalSemiring R

instance [NonAssocSemiring R] : NonAssocSemiring Rᵒᵈ := inferInstanceAs <| NonAssocSemiring R

instance [Semiring R] : Semiring Rᵒᵈ := inferInstanceAs <| Semiring R

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵒᵈ :=
  inferInstanceAs <| NonUnitalCommSemiring R

instance [CommSemiring R] : CommSemiring Rᵒᵈ := inferInstanceAs <| CommSemiring R

instance [Mul R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ := inferInstanceAs <| HasDistribNeg R

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵒᵈ :=
  inferInstanceAs <| NonUnitalNonAssocRing R

instance [NonUnitalRing R] : NonUnitalRing Rᵒᵈ := inferInstanceAs <| NonUnitalRing R

instance [NonAssocRing R] : NonAssocRing Rᵒᵈ := inferInstanceAs <| NonAssocRing R

instance [Ring R] : Ring Rᵒᵈ := inferInstanceAs <| Ring R

instance [NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ := inferInstanceAs <| NonUnitalCommRing R

instance [CommRing R] : CommRing Rᵒᵈ := inferInstanceAs <| CommRing R

instance [Ring R] [IsDomain R] : IsDomain Rᵒᵈ := inferInstanceAs <| IsDomain R

end OrderDual

open OrderDual

@[simp]
theorem toDual_natCast [NatCast R] (n : ℕ) : toDual (n : R) = n :=
  rfl

@[simp]
theorem toDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (toDual (ofNat(n) : R)) = ofNat(n) :=
  rfl

@[simp]
theorem ofDual_natCast [NatCast R] (n : ℕ) : (ofDual n : R) = n :=
  rfl

@[simp]
theorem ofDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (ofDual (ofNat(n) : Rᵒᵈ)) = ofNat(n) :=
  rfl

@[simp] lemma toDual_intCast [IntCast R] (n : ℤ) : toDual (n : R) = n := rfl

@[simp] lemma ofDual_intCast [IntCast R] (n : ℤ) : (ofDual n : R) = n := rfl

/-! ### Lexicographical order -/

namespace Lex

instance [Distrib R] : Distrib (Lex R) := inferInstanceAs <| Distrib R

instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass (Lex R) :=
  inferInstanceAs <| LeftDistribClass R

instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass (Lex R) :=
  inferInstanceAs <| RightDistribClass R

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (Lex R) :=
  inferInstanceAs <| NonUnitalNonAssocSemiring R

instance [NonUnitalSemiring R] : NonUnitalSemiring (Lex R) := inferInstanceAs <| NonUnitalSemiring R

instance [NatCast R] : NatCast (Lex R) := inferInstanceAs <| NatCast R

instance [IntCast R] : IntCast (Lex R) := inferInstanceAs <| IntCast R

instance [AddMonoidWithOne R] : AddMonoidWithOne (Lex R) := inferInstanceAs <| AddMonoidWithOne R

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Lex R) :=
  inferInstanceAs <| AddCommMonoidWithOne R

instance [AddGroupWithOne R] : AddGroupWithOne (Lex R) := inferInstanceAs <| AddGroupWithOne R

instance [AddCommGroupWithOne R] : AddCommGroupWithOne (Lex R) :=
  inferInstanceAs <| AddCommGroupWithOne R

instance [NonAssocSemiring R] : NonAssocSemiring (Lex R) := inferInstanceAs <| NonAssocSemiring R

instance [Semiring R] : Semiring (Lex R) := inferInstanceAs <| Semiring R

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (Lex R) :=
  inferInstanceAs <| NonUnitalCommSemiring R

instance [CommSemiring R] : CommSemiring (Lex R) := inferInstanceAs <| CommSemiring R

instance [Mul R] [HasDistribNeg R] : HasDistribNeg (Lex R) := inferInstanceAs <| HasDistribNeg R

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Lex R) :=
  inferInstanceAs <| NonUnitalNonAssocRing R

instance [NonUnitalRing R] : NonUnitalRing (Lex R) := inferInstanceAs <| NonUnitalRing R

instance [NonAssocRing R] : NonAssocRing (Lex R) := inferInstanceAs <| NonAssocRing R

instance [Ring R] : Ring (Lex R) := inferInstanceAs <| Ring R

instance [NonUnitalCommRing R] : NonUnitalCommRing (Lex R) := inferInstanceAs <| NonUnitalCommRing R

instance [CommRing R] : CommRing (Lex R) := inferInstanceAs <| CommRing R

instance [Ring R] [IsDomain R] : IsDomain (Lex R) := inferInstanceAs <| IsDomain R

end Lex

@[simp]
theorem toLex_natCast [NatCast R] (n : ℕ) : toLex (n : R) = n :=
  rfl

@[simp]
theorem toLex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    toLex (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

@[simp]
theorem ofLex_natCast [NatCast R] (n : ℕ) : (ofLex n : R) = n :=
  rfl

@[simp]
theorem ofLex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    ofLex (ofNat(n) : Lex R) = OfNat.ofNat n :=
  rfl
@[simp] lemma toLex_intCast [IntCast R] (n : ℤ) : toLex (n : R) = n := rfl

@[simp] lemma ofLex_intCast [IntCast R] (n : ℤ) : (ofLex n : R) = n := rfl
