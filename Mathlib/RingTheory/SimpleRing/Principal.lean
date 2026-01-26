import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.SimpleRing.Defs

/-!
# A commutative simple ring is a principal ideal domain

Indeed, it is a field.

-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsSimpleRing R]

instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
