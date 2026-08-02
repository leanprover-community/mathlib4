module

public import Mathlib.RingTheory.Congruence.Basic

variable {α β R R' : Type*}

namespace RingCon

section Lattice

variable [Add R] [Mul R] [Add R'] [Mul R'] {c d : RingCon R}

open scoped Function

-- This one probably needs the RingCon version of `Setoid.comap_surjective`
proof_wanted comap_ringConGen_equiv
    {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R] [EquivLike F R' R]
    (r : R → R → Prop) (f : F) :
    (ringConGen r).comap f = ringConGen (r on f)

end Lattice

end RingCon
