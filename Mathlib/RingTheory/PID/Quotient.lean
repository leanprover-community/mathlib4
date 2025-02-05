/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!

# Quotients of principal ideal rings

We show that quotients of PIRs are PIRs,
which implies that all (commutative) PIR have krull dimension at most 1.

-/

instance {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (I : Ideal R) :
    IsPrincipalIdealRing (R ⧸ I) :=
  .of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

instance (priority := 900) {R : Type*} [CommRing R] [IsPrincipalIdealRing R] :
    Ring.KrullDimLE 1 R := by
  refine .mk₁ fun I hI ↦ or_iff_not_imp_left.mpr fun H ↦ ?_
  obtain ⟨p, hp, hpI⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ I)
  have : p.IsPrime := hp.1.1
  have : (I.map (Ideal.Quotient.mk p)).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hpI' : ¬ I ≤ p := fun H' ↦ H ((H'.antisymm hpI) ▸ hp)
  rw [← sup_eq_left.mpr hpI, ← p.mk_ker,
    ← Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
  have := (I.map (Ideal.Quotient.mk p)).isMaximal_of_isPrime_of_ne_bot
    (by rwa [ne_eq, ← le_bot_iff, Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker])
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
