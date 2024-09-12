/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Algebra

/-!
# Characteristic of subrings
-/


universe u v

namespace CharP

instance subsemiring (R : Type u) [Semiring R] (p : ℕ) [CharP R p] (S : Subsemiring R) :
    CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h => Subtype.eq <| show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, RingHom.map_zero]⟩⟩

instance subring (R : Type u) [Ring R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h => Subtype.eq <| show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, RingHom.map_zero]⟩⟩

instance subring' (R : Type u) [CommRing R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  CharP.subring R p S

/-- The characteristic of a division ring is equal to the characteristic
  of its center-/
theorem center_char_eq_iff {R : Type u} [DivisionRing R] {p : ℕ} :
    CharP R p ↔ CharP (Subring.center R) p :=
  (@RingHom.charP_iff (Subring.center R) R _ _ (algebraMap (Subring.center R) R)
    (NoZeroSMulDivisors.algebraMap_injective (Subring.center R) R) p).symm

end CharP
