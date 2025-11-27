/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Smooth algebras are flat

Let `A` be a smooth `R`-algebra. In this file we show that then `A` is `R`-flat.
The proof proceeds in two steps:

1. If `R` is Noetherian, let `R[X₁, ..., Xₙ] →ₐ[R] A` be surjective with kernel `I`. By
  formal smoothness we construct a section `A →ₐ[R] AdicCompletion I R[X₁, ..., Xₙ]`
  of the canonical map `AdicCompletion I R[X₁, ..., Xₙ] →ₐ[R] R[X₁, ..., Xₙ] ⧸ I ≃ₐ[R] A`.
  Since `R` is Noetherian, `AdicCompletion I R` is `R`-flat so `A` is a retract
  of a flat `R`-module and hence flat.
2. (TODO @chrisflav): In the general case, we choose a model of `A` over a finitely generated
  `ℤ`-subalgebra of `R` and apply 1.


## References

- [Conde-Lago, A short proof of smooth implies flat][condelago2016shortproofsmoothimplies]
-/

@[expose] public section

universe u v

namespace Algebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

variable {R A} in
lemma FormallySmooth.flat_of_algHom_of_isNoetherianRing {S : Type*} [CommRing S] [Algebra R S]
    (f : S →ₐ[R] A) (hf : Function.Surjective f)
    [Module.Flat R S] [IsNoetherianRing S] [FormallySmooth R A] :
    Module.Flat R A := by
  have : Module.Flat R (AdicCompletion (RingHom.ker f) S) := .trans _ S _
  refine Module.Flat.of_retract (sectionAdicCompletion f hf).toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap ?_
  ext
  simp

/-- If `A` is `R`-smooth and `R` is Noetherian, then `A` is `R`-flat. -/
instance Smooth.flat_of_isNoetherianRing [IsNoetherianRing R] [Algebra.Smooth R A] :
    Module.Flat R A := by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

end Algebra
