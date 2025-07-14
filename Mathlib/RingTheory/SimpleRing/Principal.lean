/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# A simple ring is trivially a principal ideal d

-/

variable {R : Type*} [CommRing R] [IsSimpleRing R]

instance : IsSimpleOrder (Ideal R) :=
  ⟨fun I ↦ (eq_bot_or_eq_top I.toTwoSided).imp
    -- could also be done through the `gc`?
    (by simp [TwoSidedIdeal.ext_iff, Ideal.ext_iff])
    (by simp [TwoSidedIdeal.ext_iff, Ideal.ext_iff])⟩

instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
