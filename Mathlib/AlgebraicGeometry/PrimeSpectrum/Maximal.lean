/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Localization.AsSubring

#align_import algebraic_geometry.prime_spectrum.maximal from "leanprover-community/mathlib"@"052f6013363326d50cb99c6939814a4b8eb7b301"

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

open Classical

universe u v

variable (R : Type u) [CommRing R]

/-- The maximal spectrum of a commutative ring `R` is the type of all maximal ideals of `R`. -/
@[ext]
structure MaximalSpectrum where
  asIdeal : Ideal R
  IsMaximal : asIdeal.IsMaximal
#align maximal_spectrum MaximalSpectrum

attribute [instance] MaximalSpectrum.IsMaximal

variable {R}

namespace MaximalSpectrum

instance [Nontrivial R] : Nonempty <| MaximalSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
def toPrimeSpectrum (x : MaximalSpectrum R) : PrimeSpectrum R :=
  ⟨x.asIdeal, x.IsMaximal.isPrime⟩
#align maximal_spectrum.to_prime_spectrum MaximalSpectrum.toPrimeSpectrum

theorem toPrimeSpectrum_injective : (@toPrimeSpectrum R _).Injective := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using (PrimeSpectrum.ext_iff _ _).mp h
  -- 🎉 no goals
#align maximal_spectrum.to_prime_spectrum_injective MaximalSpectrum.toPrimeSpectrum_injective

open PrimeSpectrum Set

theorem toPrimeSpectrum_range :
    Set.range (@toPrimeSpectrum R _) = { x | IsClosed ({x} : Set <| PrimeSpectrum R) } := by
  simp only [isClosed_singleton_iff_isMaximal]
  -- ⊢ range toPrimeSpectrum = {x | Ideal.IsMaximal x.asIdeal}
  ext ⟨x, _⟩
  -- ⊢ { asIdeal := x, IsPrime := IsPrime✝ } ∈ range toPrimeSpectrum ↔ { asIdeal := …
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.IsMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  -- 🎉 no goals
#align maximal_spectrum.to_prime_spectrum_range MaximalSpectrum.toPrimeSpectrum_range

/-- The Zariski topology on the maximal spectrum of a commutative ring is defined as the subspace
topology induced by the natural inclusion into the prime spectrum. -/
instance zariskiTopology : TopologicalSpace <| MaximalSpectrum R :=
  PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum
#align maximal_spectrum.zariski_topology MaximalSpectrum.zariskiTopology

instance : T1Space <| MaximalSpectrum R :=
  ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.IsMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩
      -- 🎉 no goals

theorem toPrimeSpectrum_continuous : Continuous <| @toPrimeSpectrum R _ :=
  continuous_induced_dom
#align maximal_spectrum.to_prime_spectrum_continuous MaximalSpectrum.toPrimeSpectrum_continuous

variable (R)

variable [IsDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its maximal ideals
viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot : (⨅ v : MaximalSpectrum R,
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  -- ⊢ x ∈ ⨅ (v : MaximalSpectrum R), Localization.subalgebra.ofField K (Ideal.prim …
  rw [Algebra.mem_bot, Algebra.mem_iInf]
  -- ⊢ (∀ (i : MaximalSpectrum R), x ∈ Localization.subalgebra.ofField K (Ideal.pri …
  constructor
  -- ⊢ (∀ (i : MaximalSpectrum R), x ∈ Localization.subalgebra.ofField K (Ideal.pri …
  · contrapose
    -- ⊢ ¬x ∈ range ↑(algebraMap R K) → ¬∀ (i : MaximalSpectrum R), x ∈ Localization. …
    intro hrange hlocal
    -- ⊢ False
    let denom : Ideal R := (Submodule.span R {1} : Submodule R K).colon (Submodule.span R {x})
    -- ⊢ False
    have hdenom : (1 : R) ∉ denom := by
      intro hdenom
      rcases Submodule.mem_span_singleton.mp
        (Submodule.mem_colon.mp hdenom x <| Submodule.mem_span_singleton_self x) with ⟨y, hy⟩
      exact hrange ⟨y, by rw [← mul_one <| algebraMap R K y, ← Algebra.smul_def, hy, one_smul]⟩
    rcases denom.exists_le_maximal fun h => (h ▸ hdenom) Submodule.mem_top with ⟨max, hmax, hle⟩
    -- ⊢ False
    rcases hlocal ⟨max, hmax⟩ with ⟨n, d, hd, rfl⟩
    -- ⊢ False
    apply hd (hle <| Submodule.mem_colon.mpr fun _ hy => _)
    -- ⊢ ∀ (x : K), x ∈ Submodule.span R {↑(algebraMap R K) n * (↑(algebraMap R K) d) …
    intro _ hy
    -- ⊢ d • x✝ ∈ Submodule.span R {1}
    rcases Submodule.mem_span_singleton.mp hy with ⟨y, rfl⟩
    -- ⊢ d • y • (↑(algebraMap R K) n * (↑(algebraMap R K) d)⁻¹) ∈ Submodule.span R {1}
    exact Submodule.mem_span_singleton.mpr ⟨y * n, by
      rw [Algebra.smul_def, mul_one, map_mul, smul_comm, Algebra.smul_def, Algebra.smul_def,
        mul_comm <| algebraMap R K d,
        inv_mul_cancel_right₀ <|
          (map_ne_zero_iff _ <| NoZeroSMulDivisors.algebraMap_injective R K).mpr fun h =>
            (h ▸ hd) max.zero_mem]⟩
  · rintro ⟨y, rfl⟩ ⟨v, hv⟩
    -- ⊢ ↑(algebraMap R K) y ∈ Localization.subalgebra.ofField K (Ideal.primeCompl {  …
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩
    -- 🎉 no goals
#align maximal_spectrum.infi_localization_eq_bot MaximalSpectrum.iInf_localization_eq_bot

end MaximalSpectrum

namespace PrimeSpectrum

variable (R)

variable [IsDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its prime ideals
viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot : ⨅ v : PrimeSpectrum R,
    Localization.subalgebra.ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  -- ⊢ x ∈ ⨅ (v : PrimeSpectrum R), Localization.subalgebra.ofField K (Ideal.primeC …
  rw [Algebra.mem_iInf]
  -- ⊢ (∀ (i : PrimeSpectrum R), x ∈ Localization.subalgebra.ofField K (Ideal.prime …
  constructor
  -- ⊢ (∀ (i : PrimeSpectrum R), x ∈ Localization.subalgebra.ofField K (Ideal.prime …
  · rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
    -- ⊢ (∀ (i : PrimeSpectrum R), x ∈ Localization.subalgebra.ofField K (Ideal.prime …
    exact fun hx ⟨v, hv⟩ => hx ⟨v, hv.isPrime⟩
    -- 🎉 no goals
  · rw [Algebra.mem_bot]
    -- ⊢ x ∈ Set.range ↑(algebraMap R K) → ∀ (i : PrimeSpectrum R), x ∈ Localization. …
    rintro ⟨y, rfl⟩ ⟨v, hv⟩
    -- ⊢ ↑(algebraMap R K) y ∈ Localization.subalgebra.ofField K (Ideal.primeCompl {  …
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩
    -- 🎉 no goals
#align prime_spectrum.infi_localization_eq_bot PrimeSpectrum.iInf_localization_eq_bot

end PrimeSpectrum
