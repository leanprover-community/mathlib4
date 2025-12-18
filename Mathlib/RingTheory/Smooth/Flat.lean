/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Smooth algebras are flat

Let `A` be a smooth `R`-algebra. In this file we show that then `A` is `R`-flat.
The proof proceeds in two steps:

1. If `R` is Noetherian, let `R[X₁, ..., Xₙ] →ₐ[R] A` be surjective with kernel `I`. By
  formal smoothness we construct a section `A →ₐ[R] AdicCompletion I R[X₁, ..., Xₙ]`
  of the canonical map `AdicCompletion I R[X₁, ..., Xₙ] →ₐ[R] R[X₁, ..., Xₙ] ⧸ I ≃ₐ[R] A`.
  Since `R` is Noetherian, `AdicCompletion I R` is `R`-flat so `A` is a retract
  of a flat `R`-module and hence flat.
2. In the general case, we choose a model of `A` over a finitely generated
  `ℤ`-subalgebra of `R` and apply 1.


## References

- [Conde-Lago, A short proof of smooth implies flat][condelago2016shortproofsmoothimplies]
-/

@[expose] public section

namespace Algebra

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]

lemma FormallySmooth.flat_of_algHom_of_isNoetherianRing (f : S →ₐ[R] A) (hf : Function.Surjective f)
    [Module.Flat R S] [IsNoetherianRing S] [FormallySmooth R A] :
    Module.Flat R A := by
  have : Module.Flat R (AdicCompletion (RingHom.ker f) S) := .trans _ S _
  obtain ⟨g, hg⟩ := exists_kerProj_comp_eq_id f hf
  exact .of_retract g.toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap (LinearMap.ext fun x ↦ congr($hg x))

variable (R A)

/-- If `A` is `R`-smooth and `R` is Noetherian, then `A` is `R`-flat. -/
theorem Smooth.flat_of_isNoetherianRing [IsNoetherianRing R] [Smooth R A] :
    Module.Flat R A := by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

/-- Any smooth algebra is flat. -/
instance Smooth.flat [Smooth R A] : Module.Flat R A := by
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_finiteType ℤ R A
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Module.Flat A₀ B₀ := Smooth.flat_of_isNoetherianRing _ _
  exact .of_linearEquiv e.toLinearEquiv

end Algebra
