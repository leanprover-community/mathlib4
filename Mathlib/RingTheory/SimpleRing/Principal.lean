/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# A commutative simple ring is a principal ideal domain

Indeed, it is a field.

-/

variable {R : Type*} [CommRing R] [IsSimpleRing R]

instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
