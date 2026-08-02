module

public import Mathlib.RingTheory.SimpleModule.Basic

variable (R S : Type*) [Ring R] [Ring S]

variable {R S}

namespace IsSemisimpleModule

section

variable {M' : Type*} [AddCommGroup M'] [Module R M'] {N'} [AddCommGroup N'] [Module S N']
  {σ : R →+* S} (l : M' →ₛₗ[σ] N')

-- TODO: generalize Submodule.equivMapOfInjective from InvPair to RingHomSurjective
proof_wanted _root_.LinearMap.isSemisimpleModule_of_injective (_ : Function.Injective l)
    [IsSemisimpleModule S N'] : IsSemisimpleModule R M'

--TODO: generalize LinearMap.quotKerEquivOfSurjective to SemilinearMaps + RingHomSurjective
proof_wanted _root_.LinearMap.isSemisimpleModule_of_surjective (_ : Function.Surjective l)
    [IsSemisimpleModule R M'] : IsSemisimpleModule S N'

end

end IsSemisimpleModule
