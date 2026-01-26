import Mathlib.RingTheory.Finiteness.Defs

/-!
# Separation quotient is a finite module

In this file we show that the separation quotient of a finite module is a finite module.
-/

@[expose] public section

/-- The separation quotient of a finite module is a finite module. -/
instance SeparationQuotient.instModuleFinite
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] :
    Module.Finite R (SeparationQuotient M) :=
  Module.Finite.of_surjective (mkCLM R M).toLinearMap Quotient.mk_surjective
