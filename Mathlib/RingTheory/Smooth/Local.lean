/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Formally smooth local algebras
-/

public section

open TensorProduct IsLocalRing KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]

namespace Algebra

/--
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation such that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I/I² → k ⊗ₚ Ω[P/R]` is injective,
where `k` is the residue field of `S`.
-/
theorem FormallySmooth.iff_injective_lTensor_residueField.{u}
    (P : Algebra.Extension.{u} R S)
    [FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    (h' : P.ker.FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (P.cotangentComplex.lTensor (ResidueField S)) := by
  have : Module.Finite P.Ring P.Cotangent :=
    have : Module.Finite P.Ring P.ker := .of_fg h'
    .of_surjective _ Extension.Cotangent.mk_surjective
  have : Module.Finite S P.Cotangent := Module.Finite.of_restrictScalars_finite P.Ring _ _
  rw [← IsLocalRing.split_injective_iff_lTensor_residueField_injective,
    P.formallySmooth_iff_split_injection]

set_option backward.isDefEq.respectTransparency false in
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
    (P : Type*) [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (cotangentComplexBaseChange R S P (ResidueField S)) := by
  let P' : Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq h₁ }
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P' h₂]
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex (ResidueField S)]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _
    Ω[P'.Ring⁄R]).comp_injective _).symm
  exact (((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _ P'.ker).symm ≪≫ₗ
    P'.cotangentEquiv.baseChange (A := _)).injective_comp _).symm

/--
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation such that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I → k ⊗ₚ Ω[P/R]` is injective,
where `k` any field extension of the residue field of `S`.
-/
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange
    (P K : Type*) [Field K] [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [Algebra S K] [Algebra P K] [IsScalarTower P S K]
    [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG)
    (h₃ : maximalIdeal S ≤ RingHom.ker (algebraMap S K)) :
    Algebra.FormallySmooth R S ↔ Function.Injective (cotangentComplexBaseChange R S P K) := by
  let f : ResidueField S →ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) h₃
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P (ResidueField S) K := .to₁₃₄ _ S _ _
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P h₁ h₂,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective _ K]
  have : (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).toLinearMap ∘ₗ
      (cotangentComplexBaseChange R S P (ResidueField S)).baseChange K ∘ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.toLinearMap =
      (cotangentComplexBaseChange R S P K) := by
    ext; simp [cotangentComplexBaseChange_tmul]
  rw [← this]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).comp_injective _).symm
  exact ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.injective_comp _).symm

end Algebra
