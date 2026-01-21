/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu, Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The fiber of a ring homomorphism at a prime ideal

## Main results

* `Ideal.Fiber`: `p.Fiber S` is the fiber of a prime `p` of `R` in an `R`-algebra `S`,
  defined to be `κ(p) ⊗ S`.
* `PrimeSpectrum.preimageHomeomorphFiber` : We show that there is a homeomorphism between the
  fiber of the induced map `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal `p` and
  the prime spectrum of `p.Fiber S`.
-/

@[expose] public section

open Algebra TensorProduct nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

lemma Ideal.ResidueField.exists_smul_eq_tmul_one
    (x : S ⊗[R] p.ResidueField) : ∃ r ∉ p, ∃ s, r • x = s ⊗ₜ[R] 1 := by
  obtain ⟨t, r, a, hrt, e⟩ := RingHom.SurjectiveOnStalks.exists_mul_eq_tmul
    p.surjectiveOnStalks_residueField x ⊥ isPrime_bot
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl t
  simp only [smul_def, Submodule.mem_bot, mul_eq_zero, algebraMap_residueField_eq_zero,
    IsLocalRing.residue_eq_zero_iff, not_or, IsLocalization.AtPrime.mk'_mem_maximal_iff] at hrt
  refine ⟨r * y, p.primeCompl.mul_mem hrt.1 hrt.2, y • a, ?_⟩
  rw [Algebra.smul_def, ← Algebra.TensorProduct.includeRight.commutes, smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.includeRight_apply]
  simpa [← tmul_smul, Submonoid.smul_def, ← smul_mul_assoc, smul_comm _ r,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← algebraMap.coe_smul,
    ← IsScalarTower.algebraMap_apply] using congr(t • $e)

/-- The fiber of a prime `p` of `R` in an `R`-algebra `S`, defined to be `κ(p) ⊗ S`.

See `PrimeSpectrum.preimageHomeomorphFiber` for the homeomorphism between the spectrum of it
and the actual set-theoretic fiber of `PrimeSpectrum S → PrimeSpectrum R` at `p`. -/
abbrev Ideal.Fiber (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S] : Type _ :=
  p.ResidueField ⊗[R] S

lemma Ideal.Fiber.exists_smul_eq_one_tmul (x : p.Fiber S) : ∃ r ∉ p, ∃ s, r • x = 1 ⊗ₜ[R] s := by
  obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one _
    (Algebra.TensorProduct.comm _ _ _ x)
  refine ⟨r, hr, s, by simpa using congr((Algebra.TensorProduct.comm _ _ _).symm $e)⟩

variable (R S) in
/-- The fiber `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal
`p : PrimeSpectrum R` is in bijection with the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps]
noncomputable def PrimeSpectrum.preimageEquivFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ PrimeSpectrum (p.asIdeal.Fiber S) where
  toFun q := ⟨RingHom.ker (Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId _ _) congr($(q.2.symm).asIdeal))
      (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _).toRingHom, RingHom.ker_isPrime _⟩
  invFun q := ⟨q.comap Algebra.TensorProduct.includeRight.toRingHom, by
    simp only [AlgHom.toRingHom_eq_coe, Set.mem_preimage, ← comap_comp_apply,
      AlgHom.comp_algebraMap_of_tower]
    exact (residueField_comap _).le ⟨q.comap (algebraMap _ _), rfl⟩⟩
  left_inv q := by ext x; simp
  right_inv q := by
    ext x
    obtain ⟨r, hr, s, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ x
    have := @PrimeSpectrum.isPrime -- times out if removed
    rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), iff_comm,
      ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), ← Algebra.smul_def, e]
    · simp
    · rw [← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal]
      convert hr
      exact (residueField_comap _).le ⟨q.comap (algebraMap _ _), rfl⟩
    · simpa [-Algebra.algebraMap_self, -AlgHom.commutes, -AlgHom.map_algebraMap,
        -Ideal.ResidueField.map_algebraMap]

variable (R S) in
/-- The `OrderIso` between the fiber of `PrimeSpectrum S → PrimeSpectrum R` at a prime
ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def PrimeSpectrum.preimageOrderIsoFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃o PrimeSpectrum (p.asIdeal.Fiber S) where
  toEquiv := preimageEquivFiber R S p
  map_rel_iff' {q₁ q₂} := by
    constructor
    · obtain ⟨q₁, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₁
      obtain ⟨q₂, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₂
      simpa using Ideal.comap_mono
    · intro H x hx
      obtain ⟨r, hr, s, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ x
      rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), ← Algebra.smul_def, e] at hx ⊢
      · replace hx : s ∈ q₁.1.asIdeal := by simpa using hx
        simpa using H hx
      · rw [← q₂.2] at hr; simpa [IsScalarTower.algebraMap_apply R S q₂.1.asIdeal.ResidueField]
      · rw [← q₁.2] at hr; simpa [IsScalarTower.algebraMap_apply R S q₁.1.asIdeal.ResidueField]

@[deprecated (since := "2025-12-07")]
alias PrimeSpectrum.preimageOrderIsoTensorResidueField := PrimeSpectrum.preimageOrderIsoFiber

variable (R S) in
/-- The `OrderIso` between the set of primes lying over a prime ideal `p : Ideal R`,
and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def PrimeSpectrum.primesOverOrderIsoFiber (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    p.primesOver S ≃o PrimeSpectrum (p.Fiber S) :=
  .trans ⟨⟨fun q ↦ ⟨⟨q, q.2.1⟩, PrimeSpectrum.ext q.2.2.1.symm⟩,
    fun q ↦ ⟨q.1.asIdeal, ⟨q.1.2, ⟨congr($(q.2).1).symm⟩⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩
    (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p, ‹_›⟩)

/-- The `Homeomorph` between the fiber of `PrimeSpectrum S → PrimeSpectrum R`
at a prime ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def PrimeSpectrum.preimageHomeomorphFiber (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ₜ PrimeSpectrum (p.asIdeal.Fiber S) := by
  letI H : Topology.IsEmbedding (preimageOrderIsoFiber R S p).symm := by
    refine (Topology.IsEmbedding.of_comp_iff .subtypeVal).mp ?_
    have := PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks _ S _
      (Ideal.surjectiveOnStalks_residueField p.asIdeal)
    exact ((Homeomorph.prodUnique _ _).isEmbedding.comp this).comp
      (homeomorphOfRingEquiv (Algebra.TensorProduct.comm _ _ _).toRingEquiv).isEmbedding
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
