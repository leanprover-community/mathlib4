/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Submodule.Order
import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Order instances on subalgebras
-/

namespace Subalgebra

variable {R A : Type*}

instance toIsOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedRing A]
    [Algebra R A] (S : Subalgebra R A) : IsOrderedRing S :=
  S.toSubsemiring.toIsOrderedRing

instance toIsStrictOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A]
    [IsStrictOrderedRing A] [Algebra R A] (S : Subalgebra R A) : IsStrictOrderedRing S :=
  S.toSubsemiring.toIsStrictOrderedRing

end Subalgebra
