/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Submodule.Order
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.Algebra.Ring.Subring.Order

/-!
# Order instances on subalgebras
-/

namespace Subalgebra

variable {R A : Type*}

instance toOrderedSemiring [CommSemiring R] [OrderedSemiring A] [Algebra R A]
    (S : Subalgebra R A) : OrderedSemiring S :=
  S.toSubsemiring.toOrderedSemiring

instance toStrictOrderedSemiring [CommSemiring R] [StrictOrderedSemiring A] [Algebra R A]
    (S : Subalgebra R A) : StrictOrderedSemiring S :=
  S.toSubsemiring.toStrictOrderedSemiring

instance toOrderedCommSemiring [CommSemiring R] [OrderedCommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : OrderedCommSemiring S :=
  S.toSubsemiring.toOrderedCommSemiring

instance toStrictOrderedCommSemiring [CommSemiring R] [StrictOrderedCommSemiring A]
    [Algebra R A] (S : Subalgebra R A) : StrictOrderedCommSemiring S :=
  S.toSubsemiring.toStrictOrderedCommSemiring

instance toOrderedRing [CommRing R] [OrderedRing A] [Algebra R A] (S : Subalgebra R A) :
    OrderedRing S :=
  S.toSubring.toOrderedRing

instance toOrderedCommRing [CommRing R] [OrderedCommRing A] [Algebra R A]
    (S : Subalgebra R A) : OrderedCommRing S :=
  S.toSubring.toOrderedCommRing

instance toLinearOrderedSemiring [CommSemiring R] [LinearOrderedSemiring A] [Algebra R A]
    (S : Subalgebra R A) : LinearOrderedSemiring S :=
  S.toSubsemiring.toLinearOrderedSemiring

instance toLinearOrderedCommSemiring [CommSemiring R] [LinearOrderedCommSemiring A]
    [Algebra R A] (S : Subalgebra R A) : LinearOrderedCommSemiring S :=
  S.toSubsemiring.toLinearOrderedCommSemiring

instance toLinearOrderedRing [CommRing R] [LinearOrderedRing A] [Algebra R A]
    (S : Subalgebra R A) : LinearOrderedRing S :=
  S.toSubring.toLinearOrderedRing

instance toLinearOrderedCommRing [CommRing R] [LinearOrderedCommRing A] [Algebra R A]
    (S : Subalgebra R A) : LinearOrderedCommRing S :=
  S.toSubring.toLinearOrderedCommRing

end Subalgebra
