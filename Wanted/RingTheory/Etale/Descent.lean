module

public import Mathlib.RingTheory.Etale.Descent

open TensorProduct

namespace Algebra

/-- Formally smooth algebras descend along faithfully flat base change. See the TODO
in the module docstring of `Mathlib/RingTheory/Etale/Descent.lean`. -/
proof_wanted FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [FormallySmooth T (T ⊗[R] S)] :
    FormallySmooth R S

end Algebra
