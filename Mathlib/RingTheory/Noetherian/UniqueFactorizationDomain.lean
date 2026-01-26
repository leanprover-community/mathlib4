import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
/-!
# Noetherian domains have unique factorization

## Main results

- IsNoetherianRing.wfDvdMonoid
-/

@[expose] public section

variable {R : Type*} [CommSemiring R] [IsDomain R]

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherianRing.wfDvdMonoid [h : IsNoetherianRing R] :
    WfDvdMonoid R :=
  WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt h.wf.wellFoundedOn
