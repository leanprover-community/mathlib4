/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Subring.Basic

#align_import algebra.char_p.subring from "leanprover-community/mathlib"@"168ad7fc5d8173ad38be9767a22d50b8ecf1cd00"

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
                                                        -- 🎉 no goals
          map_natCast S.subtype x ▸ by rw [h, RingHom.map_zero]⟩⟩
                                       -- 🎉 no goals
#align char_p.subsemiring CharP.subsemiring

instance subring (R : Type u) [Ring R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h => Subtype.eq <| show S.subtype x = 0 by rw [map_natCast, h], fun h =>
                                                        -- 🎉 no goals
          map_natCast S.subtype x ▸ by rw [h, RingHom.map_zero]⟩⟩
                                       -- 🎉 no goals
#align char_p.subring CharP.subring

instance subring' (R : Type u) [CommRing R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  CharP.subring R p S
#align char_p.subring' CharP.subring'

end CharP
