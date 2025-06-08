/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
/-!
# Noetherian domains have unique factorization

## Main results

# IsNoetherianRing.wfDvdMonoid
-/

variable {R : Type*} [CommSemiring R] [IsDomain R]

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherianRing.wfDvdMonoid [h : IsNoetherianRing R] :
    WfDvdMonoid R :=
  WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt h.wf.wellFoundedOn
