/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu, Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The fiber at a prime ideal

## Main definitions

* `Ideal.Fiber`: `p.Fiber S` is the fiber of a prime `p` of `R` in an `R`-algebra `S`,
  defined to be `κ(p) ⊗ S`.
-/

@[expose] public section

open Algebra TensorProduct nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
instance [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (ResidueField R ⊗[R] S) :=
  let eSp : ResidueField R ⊗[R] S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.comm _ _ _).trans
      ((TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)
  have : Nontrivial (IsLocalRing.ResidueField R ⊗[R] S) := by
    rw [eSp.nontrivial_congr, Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).lt_top).ne
  .of_surjective' TensorProduct.includeRight.toRingHom
    (TensorProduct.mk_surjective _ _ _ residue_surjective)

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

instance (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] : q.LiesOver p :=
  .trans _ (⊥ : Ideal p.ResidueField) _

lemma Ideal.Fiber.exists_smul_eq_one_tmul (x : p.Fiber S) : ∃ r ∉ p, ∃ s, r • x = 1 ⊗ₜ[R] s := by
  obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one _
    (Algebra.TensorProduct.comm _ _ _ x)
  refine ⟨r, hr, s, by simpa using congr((Algebra.TensorProduct.comm _ _ _).symm $e)⟩
