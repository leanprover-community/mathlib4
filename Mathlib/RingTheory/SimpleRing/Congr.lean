/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Simpleness is preserved by ring isomorphism

If `R` is a simple ring then any ring isomorphic to `R` is also simple.
-/

namespace IsSimpleRing

lemma of_ringEquiv {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R ≃+* S) (h : IsSimpleRing R) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder (TwoSidedIdeal.orderIsoOfRingEquiv f.symm)

end IsSimpleRing
