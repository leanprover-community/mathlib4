import Mathlib

set_option trace.Meta.synthInstance true

example {R S T ι : Type*}
    [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Generators R S ι) [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    RingHom.ker (algebraMap (P.ofAlgEquiv e).Ring T) = sorry := by
  simp
-- master: simp made no progress
-- #33697: failed to synthesize FaithfulSMul (P.ofAlgEquiv e).Ring T (deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

variable {R S T ι : Type*}
    [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Generators R S ι) [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)

#count_heartbeats in
#synth FaithfulSMul (P.ofAlgEquiv e).Ring T
-- master: Used 19452 heartbeats
-- #33697: Used 22693 heartbeats
-- #34475: Used 15502 heartbeats
