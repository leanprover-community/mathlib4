module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.AddCharTrace
public import Mathlib.Misc
public import Mathlib.Cyclotomic
public import Mathlib.Teichmuller
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

open NumberField

variable {K ι : Type*} [Field K] (I : Ideal (𝓞 K)) (s : Finset ι) (f : ι → 𝓞 K)

example :
    Ideal.Quotient.mk I (∑ i ∈ s, f i) = ∑ i ∈ s, Ideal.Quotient.mk I (f i) := by
--  have : AddMonoidHomClass (𝓞 K →+* 𝓞 K ⧸ I) (𝓞 K) (𝓞 K ⧸ I) :=
--    RingHomClass.toNonUnitalRingHomClass.toAddMonoidHomClass
  rw [map_sum]
