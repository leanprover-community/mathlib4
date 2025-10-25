/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu, Andrew Yang
-/
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The fiber of a ring homomorphism at a prime ideal

## Main results

* `PrimeSpectrum.preimageOrderIsoTensorResidueField` : We show that there is an `OrderIso` between
  fiber of a ring homomorphism `algebraMap R S : R →+* S` at a prime ideal `p : PrimeSpectrum R` and
  the prime spectrum of the tensor product of `S` and the residue field of `p`.
-/

open Algebra TensorProduct nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

lemma Ideal.ResidueField.exists_smul_eq_tensor_one
    (x : S ⊗[R] p.ResidueField) : ∃ r ∉ p, ∃ s, r • x = s ⊗ₜ[R] 1 := by
  obtain ⟨t, r, a, hrt, e⟩ := RingHom.SurjectiveOnStalks.exists_mul_eq_tmul
    p.surjectiveOnStalks_residueField x ⊥ bot_prime
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
  obtain ⟨y, t, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl t
  simp only [smul_def, Submodule.mem_bot, mul_eq_zero, algebraMap_residueField_eq_zero,
    IsLocalRing.residue_eq_zero_iff, not_or, IsLocalization.AtPrime.mk'_mem_maximal_iff] at hrt
  refine ⟨r * y, p.primeCompl.mul_mem hrt.1 hrt.2, y • a, ?_⟩
  rw [Algebra.smul_def, ← Algebra.TensorProduct.includeRight.commutes, smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.includeRight_apply]
  simpa [← tmul_smul, Submonoid.smul_def, ← smul_mul_assoc, smul_comm _ r,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← algebraMap.coe_smul,
    ← IsScalarTower.algebraMap_apply] using congr(t • $e)

lemma Ideal.ResidueField.exists_smul_eq_one_tensor
    (x : p.ResidueField ⊗[R] S) : ∃ r ∉ p, ∃ s, r • x = 1 ⊗ₜ[R] s := by
  obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_tensor_one _
    (Algebra.TensorProduct.comm _ _ _ x)
  refine ⟨r, hr, s, by simpa using congr((Algebra.TensorProduct.comm _ _ _).symm $e)⟩

variable (R S) in
/-- The fiber of a ring homomorphism `algebraMap R S : R →+* S` at a prime ideal
`p : PrimeSpectrum R` is in bijection with the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps]
noncomputable def PrimeSpectrum.preimageEquivTensorResidueField (p : PrimeSpectrum R) :
    (algebraMap R S).specComap ⁻¹' {p} ≃
      PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] S) where
  toFun q := ⟨RingHom.ker (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal congr($(q.2.symm).asIdeal))
          (IsScalarTower.toAlgHom _ _ _) (fun _ _ ↦ .all _ _)).toRingHom, RingHom.ker_isPrime _⟩
  invFun q := ⟨Algebra.TensorProduct.includeRight.toRingHom.specComap q, by
    simp only [AlgHom.toRingHom_eq_coe, Set.mem_preimage, ← specComap_comp_apply,
      AlgHom.comp_algebraMap_of_tower]
    exact (residueField_specComap _).le ⟨(algebraMap _ _).specComap q, rfl⟩⟩
  left_inv q := by ext x; simp
  right_inv q := by
    ext x
    obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_one_tensor _ x
    have := @PrimeSpectrum.isPrime -- times out if removed
    rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), iff_comm,
      ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), ← Algebra.smul_def, e]
    · simp
    · rw [← Ideal.mem_comap, ← PrimeSpectrum.specComap_asIdeal]
      convert hr
      exact (residueField_specComap _).le ⟨(algebraMap _ _).specComap q, rfl⟩
    · simpa [-Algebra.algebraMap_self, -AlgHom.commutes, -AlgHom.map_algebraMap]

variable (R S) in
/-- The `OrderIso` between fiber of a ring homomorphism `algebraMap R S : R →+* S` at a prime ideal
`p : PrimeSpectrum R` and the prime spectrum of the tensor product of `S` and the residue field of
`p`. -/
@[simps!]
noncomputable def PrimeSpectrum.preimageOrderIsoTensorResidueField (p : PrimeSpectrum R) :
    (algebraMap R S).specComap ⁻¹' {p} ≃o
      PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] S) where
  toEquiv := preimageEquivTensorResidueField R S p
  map_rel_iff' {q₁ q₂} := by
    constructor
    · obtain ⟨q₁, rfl⟩ := (preimageEquivTensorResidueField R S p).symm.surjective q₁
      obtain ⟨q₂, rfl⟩ := (preimageEquivTensorResidueField R S p).symm.surjective q₂
      simpa using Ideal.comap_mono
    · intro H x hx
      obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_one_tensor _ x
      rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ r), ← Algebra.smul_def, e] at hx ⊢
      · replace hx : s ∈ q₁.1.asIdeal := by simpa using hx
        simpa using H hx
      · rw [← q₂.2] at hr; simpa [IsScalarTower.algebraMap_apply R S q₂.1.asIdeal.ResidueField]
      · rw [← q₁.2] at hr; simpa [IsScalarTower.algebraMap_apply R S q₁.1.asIdeal.ResidueField]
