/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Topology.KrullDimension

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring theoretic Krull dimension is the order theoretic Krull dimension
applied to its prime spectrum. Unfolding this definition, it is the length of the longest series of
prime ideals ordered by inclusion.

Key results in this file include:
1. the ring theoretic Krull dimension of a commutative ring is equal to the topological Krull
   dimension of its prime spectrum;
2. given a surjective homomorphism `f : R →+* S` of commutative rings, the Krull dimension of `S`
   cannot exceed that of `R`;
3. the Krull dimension of any quotient ring of a commutative ring must be less than or equal to
   the Krull dimension of that commutative ring;
4. two isomorphic commutative rings have the same Krull dimension;
5. the Krull dimension of a field is zero.
-/

/--
The ring theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
-/
noncomputable abbrev ringKrullDim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

open PrimeSpectrum OrderDual in
theorem eq_topologicalKrullDim (R : Type _) [CommRing R] :
    ringKrullDim R = topologicalKrullDim (PrimeSpectrum R) :=
  Eq.symm $ krullDim_orderDual.symm.trans $ krullDim_eq_of_orderIso $ OrderIso.symm {
    toFun := fun p ↦ ⟨zeroLocus p.asIdeal, isIrreducible_zeroLocus_iff _ |>.mpr <| by
      simpa only [p.isPrime.radical] using p.isPrime, isClosed_zeroLocus p.asIdeal⟩
    invFun := fun s ↦ ⟨vanishingIdeal s.1, isIrreducible_iff_vanishingIdeal_isPrime.mp s.2⟩
    left_inv := fun p ↦ PrimeSpectrum.ext _ _ <| by
      simp_rw [vanishingIdeal_zeroLocus_eq_radical, p.isPrime.radical]
    right_inv := fun s ↦ by
      simp only [zeroLocus_vanishingIdeal_eq_closure, s.3.closure_eq]; rfl
    map_rel_iff' := by
      intro p q
      change zeroLocus _ ≤ zeroLocus _ ↔ _
      simp [zeroLocus_subset_zeroLocus_iff, q.isPrime.radical] }

/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
theorem le_of_surj (R S : Type _) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (PrimeSpectrum.comap f) (Monotone.strictMono_of_injective
    (fun _ _ hab ↦ Ideal.comap_mono hab) (PrimeSpectrum.comap_injective_of_surjective f hf))

/-- If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`. -/
theorem le_of_quot (R : Type _) [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  le_of_surj _ _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
theorem eq_of_ringEquiv (R S : Type _) [CommRing R] [CommRing S] (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (le_of_surj S R (RingEquiv.symm e) (EquivLike.surjective (RingEquiv.symm e)))
    (le_of_surj R S e (EquivLike.surjective e))

section Field

theorem eq_zero_of_field (F : Type _) [Field F] : ringKrullDim F = 0 :=
  krullDim_eq_zero_of_unique

theorem eq_zero_of_isField (F : Type _) [CommRing F] (hF : IsField F) : ringKrullDim F = 0 :=
  @krullDim_eq_zero_of_unique _ _ <| @PrimeSpectrum.instUnique _ hF.toField

end Field

end ringKrullDim
