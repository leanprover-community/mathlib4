/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.PrimeSpectrum
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Maximal spectrum of a commutative ring

The maximal spectrum of a commutative ring is the type of all maximal ideals.
It is naturally a subset of the prime spectrum endowed with the subspace topology.

## Main definitions

* `MaximalSpectrum R`: The maximal spectrum of a commutative ring `R`,
  i.e., the set of all maximal ideals of `R`.

## Implementation notes

The Zariski topology on the maximal spectrum is defined as the subspace topology induced by the
natural inclusion into the prime spectrum to avoid API duplication for zero loci.
-/


noncomputable section

open scoped Classical

universe u v

variable (R : Type u) [CommRing R]

/-- The maximal spectrum of a commutative ring `R` is the type of all maximal ideals of `R`. -/
@[ext]
structure MaximalSpectrum where
  asIdeal : Ideal R
  IsMaximal : asIdeal.IsMaximal

attribute [instance] MaximalSpectrum.IsMaximal

variable {R}

namespace MaximalSpectrum

instance [Nontrivial R] : Nonempty <| MaximalSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
def toPrimeSpectrum (x : MaximalSpectrum R) : PrimeSpectrum R :=
  ⟨x.asIdeal, x.IsMaximal.isPrime⟩

theorem toPrimeSpectrum_injective : (@toPrimeSpectrum R _).Injective := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using PrimeSpectrum.ext_iff.mp h

open PrimeSpectrum Set

variable (R)
variable [IsDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its maximal ideals
viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot : (⨅ v : MaximalSpectrum R,
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_bot, Algebra.mem_iInf]
  constructor
  · contrapose
    intro hrange hlocal
    let denom : Ideal R := (Submodule.span R {1} : Submodule R K).colon (Submodule.span R {x})
    have hdenom : (1 : R) ∉ denom := by
      intro hdenom
      rcases Submodule.mem_span_singleton.mp
        (Submodule.mem_colon.mp hdenom x <| Submodule.mem_span_singleton_self x) with ⟨y, hy⟩
      exact hrange ⟨y, by rw [← mul_one <| algebraMap R K y, ← Algebra.smul_def, hy, one_smul]⟩
    rcases denom.exists_le_maximal fun h => (h ▸ hdenom) Submodule.mem_top with ⟨max, hmax, hle⟩
    rcases hlocal ⟨max, hmax⟩ with ⟨n, d, hd, rfl⟩
    apply hd (hle <| Submodule.mem_colon.mpr fun _ hy => _)
    intro _ hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨y, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨y * n, by
      rw [Algebra.smul_def, mul_one, map_mul, smul_comm, Algebra.smul_def, Algebra.smul_def,
        mul_comm <| algebraMap R K d,
        inv_mul_cancel_right₀ <|
          (map_ne_zero_iff _ <| NoZeroSMulDivisors.algebraMap_injective R K).mpr fun h =>
            (h ▸ hd) max.zero_mem]⟩
  · rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩

end MaximalSpectrum

namespace PrimeSpectrum

variable (R)
variable [IsDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its prime ideals
viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot : ⨅ v : PrimeSpectrum R,
    Localization.subalgebra.ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  · rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
    exact fun hx ⟨v, hv⟩ => hx ⟨v, hv.isPrime⟩
  · rw [Algebra.mem_bot]
    rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩

end PrimeSpectrum
