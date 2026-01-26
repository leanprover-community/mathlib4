import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Noetherian quotient rings and quotient modules
-/

@[expose] public section

instance Ideal.Quotient.isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower R <| inferInstance
