/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.Congruence.Basic

variable {R R' : Type*}

namespace RingCon

variable [Add R] [Mul R] [Add R'] [Mul R']

open scoped Function

-- This probably needs the RingCon version of `Setoid.comap_surjective`
proof_wanted comap_ringConGen_equiv
    {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R] [EquivLike F R' R]
    (r : R → R → Prop) (f : F) :
    (ringConGen r).comap f = ringConGen (r on f)

end RingCon
