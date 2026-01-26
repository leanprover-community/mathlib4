import Mathlib.Algebra.Order.Ring.Defs

/-!
# Order instances on subalgebras
-/

@[expose] public section

namespace Subalgebra

variable {R A : Type*}

instance toIsOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedRing A]
    [Algebra R A] (S : Subalgebra R A) : IsOrderedRing S :=
  S.toSubsemiring.toIsOrderedRing

instance toIsStrictOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A]
    [IsStrictOrderedRing A] [Algebra R A] (S : Subalgebra R A) : IsStrictOrderedRing S :=
  S.toSubsemiring.toIsStrictOrderedRing

end Subalgebra
