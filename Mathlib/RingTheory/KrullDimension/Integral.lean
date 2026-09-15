/-
Copyright (c) 2026 Robert Shlyakhtenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Shlyakhtenko
-/

module

public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integral extensions

In this file we prove that an injective integral homomorphism of commutative rings
preserves Krull dimension.

## Main results

- `RingHom.IsIntegral.ringKrullDim_eq_of_injective`: injective integral homomorphisms of
  commutative rings preserve Krull dimension.
- `RingHom.IsIntegral.ringKrullDim_quotient_ker_eq`: for an integral extension `f : A →+* B`,
  the Krull dimension of `B` is equal to the Krull dimension of `A ⧸ RingHom.ker f`.
-/

@[expose] public section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Given an `A`-algebra `B` with the going up property, if the induced map `Spec B → Spec A`
is surjective, then `ringKrullDim A ≤ ringKrullDim B`. -/
theorem Algebra.HasGoingUp.ringKrullDim_le_of_comap_surjective
    [Algebra A B] [Algebra.HasGoingUp A B]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    ringKrullDim A ≤ ringKrullDim B := by
  apply iSup_le
  intro l
  obtain ⟨P, hP⟩ := hsurj l.head
  have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by simp [hP.symm]⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  exact hlen ▸ le_iSup (fun L : LTSeries (PrimeSpectrum B) => (L.length : WithBot ℕ∞)) L

namespace RingHom

variable {f : A →+* B} (hf : f.IsIntegral)

include hf

/-- An integral ring homomorphism cannot increase Krull dimension. -/
theorem IsIntegral.ringKrullDim_le : ringKrullDim B ≤ ringKrullDim A :=
  let := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hf⟩
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    (fun _ _ hPQ => Ideal.IsIntegral.comap_lt_comap hPQ)

/-- An injective integral ring homomorphism preserves Krull dimension. -/
theorem IsIntegral.ringKrullDim_eq_of_injective
    (hinj : Function.Injective f) : ringKrullDim A = ringKrullDim B :=
  let := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hf⟩
  le_antisymm (Algebra.HasGoingUp.ringKrullDim_le_of_comap_surjective
    (hf.comap_surjective hinj)) (RingHom.IsIntegral.ringKrullDim_le hf)

/-- A generalized version of `RingHom.IsIntegral.ringKrullDim_eq_of_injective`.
For an integral extension `f : A →+* B`, the Krull dimension of `B`
is equal to the Krull dimension of `A ⧸ RingHom.ker f`. -/
theorem IsIntegral.ringKrullDim_quotient_ker_eq :
    ringKrullDim (A ⧸ RingHom.ker f) = ringKrullDim B :=
  RingHom.IsIntegral.ringKrullDim_eq_of_injective hf.kerLift f.kerLift_injective

end RingHom
