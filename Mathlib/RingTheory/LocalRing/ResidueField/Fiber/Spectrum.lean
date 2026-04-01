/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu, Andrew Yang, Thomas Browning
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The spectrum of the fiber at a prime ideal

## Main results

* `PrimeSpectrum.preimageHomeomorphFiber` : We show that there is a homeomorphism between the
  fiber of the induced map `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal `p` and
  the prime spectrum of `p.Fiber S`.
-/

@[expose] public section

namespace PrimeSpectrum

open Algebra TensorProduct nonZeroDivisors

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- The fiber `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal
`p : PrimeSpectrum R` is in bijection with the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps]
noncomputable def preimageEquivFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ PrimeSpectrum (p.asIdeal.Fiber S) where
  toFun q := ⟨q.1.1.map (algebraMap S (p.1.Fiber S)),
    have : q.1.1.LiesOver p.1 := ⟨PrimeSpectrum.ext_iff.mp q.2.symm⟩
    inferInstance⟩
  invFun q := ⟨⟨q.1.under S, q.2.under S⟩, PrimeSpectrum.ext Ideal.LiesOver.over.symm⟩
  left_inv q := by
    let m := algebraMapSubmonoid S p.1.primeCompl
    simp only [Subtype.ext_iff, PrimeSpectrum.ext_iff, Ideal.under_def]
    rw [IsScalarTower.algebraMap_eq S (Localization m), ← Ideal.map_map, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ (Ideal.Fiber.algebraMap_localization_surjective p.1 S),
      ← RingHom.ker_eq_comap_bot, sup_of_le_left,
      IsLocalization.comap_map_of_isPrime_disjoint m _ q.1.2]
    · exact Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr q.2.le)
    · rw [Ideal.Fiber.ker_algebraMap_localization']
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr q.2.ge)
  right_inv q := by
    simp only [PrimeSpectrum.ext_iff, Ideal.under_def]
    rw [IsScalarTower.algebraMap_eq S (Localization (algebraMapSubmonoid S p.1.primeCompl)),
      ← Ideal.map_map, ← Ideal.comap_comap,
      IsLocalization.map_comap (Algebra.algebraMapSubmonoid S p.1.primeCompl),
      Ideal.map_comap_of_surjective _ (Ideal.Fiber.algebraMap_localization_surjective p.1 S)]

/-- The `OrderIso` between the fiber of `PrimeSpectrum S → PrimeSpectrum R` at a prime
ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def preimageOrderIsoFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃o PrimeSpectrum (p.asIdeal.Fiber S) where
  toEquiv := preimageEquivFiber R S p
  map_rel_iff' {q₁ q₂} := by
    constructor
    · obtain ⟨q₁, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₁
      obtain ⟨q₂, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₂
      simpa using Ideal.comap_mono
    · exact Ideal.map_mono

@[deprecated (since := "2025-12-07")]
alias preimageOrderIsoTensorResidueField := preimageOrderIsoFiber

/-- The `OrderIso` between the set of primes lying over a prime ideal `p : Ideal R`,
and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def primesOverOrderIsoFiber (p : Ideal R) [p.IsPrime] :
    p.primesOver S ≃o PrimeSpectrum (p.Fiber S) :=
  .trans ⟨⟨fun q ↦ ⟨⟨q, q.2.1⟩, PrimeSpectrum.ext q.2.2.1.symm⟩,
    fun q ↦ ⟨q.1.asIdeal, ⟨q.1.2, ⟨congr($(q.2).1).symm⟩⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩
    (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p, ‹_›⟩)

/-- The `Homeomorph` between the fiber of `PrimeSpectrum S → PrimeSpectrum R`
at a prime ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def preimageHomeomorphFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ₜ PrimeSpectrum (p.asIdeal.Fiber S) := by
  letI H : Topology.IsEmbedding (preimageOrderIsoFiber R S p).symm := by
    refine (Topology.IsEmbedding.of_comp_iff .subtypeVal).mp ?_
    simpa only [← IsScalarTower.algebraMap_eq, ← PrimeSpectrum.comap_comp] using
      (localization_comap_isEmbedding _ (algebraMapSubmonoid S p.1.primeCompl)).comp
        (isEmbedding_comap_of_surjective _ _ (Ideal.Fiber.algebraMap_localization_surjective p.1 S))
  exact
  { __ := preimageOrderIsoFiber R S p
    continuous_toFun := by
      convert (H.toHomeomorphOfSurjective
        (preimageOrderIsoFiber R S p).symm.surjective).symm.continuous
      ext1 x
      obtain ⟨x, rfl⟩ := (H.toHomeomorphOfSurjective
        (preimageOrderIsoFiber R S p).symm.surjective).surjective x
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Homeomorph.symm_apply_apply]
      simp
    continuous_invFun := H.continuous }

end PrimeSpectrum
