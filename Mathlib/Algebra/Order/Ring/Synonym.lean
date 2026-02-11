/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Algebra.Ring.InjSurj

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

@[expose] public section


open OrderDual

variable {R : Type*}

/-! ### Order dual -/

instance [NatCast R] : NatCast Rᵒᵈ where natCast n := toDual n

instance [IntCast R] : IntCast Rᵒᵈ where intCast n := toDual n

instance [Distrib R] : Distrib Rᵒᵈ :=
  ofDual_injective.distrib ofDual (fun _ _ => rfl) (fun _ _ => rfl)

instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ :=
  ofDual_injective.leftDistribClass ofDual (fun _ _ => rfl) (fun _ _ => rfl)

instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ :=
  ofDual_injective.rightDistribClass ofDual (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ :=
  ofDual_injective.nonUnitalNonAssocSemiring ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

instance [NonUnitalSemiring R] : NonUnitalSemiring Rᵒᵈ :=
  ofDual_injective.nonUnitalSemiring ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

instance [NonAssocSemiring R] : NonAssocSemiring Rᵒᵈ :=
  ofDual_injective.nonAssocSemiring ofDual rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)

instance [Semiring R] : Semiring Rᵒᵈ :=
  ofDual_injective.semiring ofDual rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵒᵈ :=
  ofDual_injective.nonUnitalCommSemiring ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

instance [CommSemiring R] : CommSemiring Rᵒᵈ :=
  ofDual_injective.commSemiring ofDual rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

instance [Mul R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ :=
  ofDual_injective.hasDistribNeg _ (fun _ => rfl) (fun _ _ => rfl)

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵒᵈ :=
  ofDual_injective.nonUnitalNonAssocRing ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonUnitalRing R] : NonUnitalRing Rᵒᵈ :=
  ofDual_injective.nonUnitalRing ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonAssocRing R] : NonAssocRing Rᵒᵈ :=
  ofDual_injective.nonAssocRing ofDual rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

instance [Ring R] : Ring Rᵒᵈ :=
  ofDual_injective.ring ofDual rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

instance [NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ :=
  ofDual_injective.nonUnitalCommRing ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [CommRing R] : CommRing Rᵒᵈ :=
  ofDual_injective.commRing ofDual rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

instance [Ring R] [IsDomain R] : IsDomain Rᵒᵈ where

/-! ### Lexicographical order -/


instance [h : Distrib R] : Distrib (Lex R) := h

instance [Mul R] [Add R] [h : LeftDistribClass R] : LeftDistribClass (Lex R) := h

instance [Mul R] [Add R] [h : RightDistribClass R] : RightDistribClass (Lex R) := h

instance [h : NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (Lex R) := h

instance [h : NonUnitalSemiring R] : NonUnitalSemiring (Lex R) := h

instance [h : NonAssocSemiring R] : NonAssocSemiring (Lex R) := h

instance [h : Semiring R] : Semiring (Lex R) := h

instance [h : NonUnitalCommSemiring R] : NonUnitalCommSemiring (Lex R) := h

instance [h : CommSemiring R] : CommSemiring (Lex R) := h

instance [Mul R] [h : HasDistribNeg R] : HasDistribNeg (Lex R) := h

instance [h : NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Lex R) := h

instance [h : NonUnitalRing R] : NonUnitalRing (Lex R) := h

instance [h : NonAssocRing R] : NonAssocRing (Lex R) := h

instance [h : Ring R] : Ring (Lex R) := h

instance [h : NonUnitalCommRing R] : NonUnitalCommRing (Lex R) := h

instance [h : CommRing R] : CommRing (Lex R) := h

instance [Ring R] [h : IsDomain R] : IsDomain (Lex R) := h
