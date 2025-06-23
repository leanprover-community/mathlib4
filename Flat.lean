/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
import Mathlib

/-!
# `RingTheory.Sequence.IsWeaklyRegular` is stable under flat base change

## Main results
* `RingTheory.Sequence.IsWeaklyRegular.of_flat_isBaseChange`: Let `R` be a commutative ring,
  `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base change of `M` to `S`.
  If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is a weakly regular
  `N`-sequence.
-/

open RingTheory.Sequence Pointwise Module TensorProduct

section FaithfullyFlat

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R)
  (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

variable (S) in
/-- `S ⧸ IS ≃ₗ[R] S ⊗[R] (R ⧸ I)`. -/
noncomputable def Ideal.qoutMapEquivTensorQout {I : Ideal R} :
    (S ⧸ Ideal.map (algebraMap R S) I) ≃ₗ[R] S ⊗[R] (R ⧸ I) :=
  LinearEquiv.symm <| tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R _

include hf

variable (R S M) in
/-- `N ⊗[S] P ≃ₗ[R] M ⊗[R] P`. -/
noncomputable def IsBaseChange.tensorEquiv : N ⊗[S] P ≃ₗ[R] M ⊗[R] P :=
  (TensorProduct.comm S _ _ ≪≫ₗ LinearEquiv.lTensor P hf.equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R S S P M).restrictScalars R ≪≫ₗ TensorProduct.comm R P M

/-- `N ⧸ IN ≃ₗ[R] S ⊗[R] (M ⧸ IM)`. -/
noncomputable def IsBaseChange.quotMapSMulEquivTensorQuot (I : Ideal R) :
    (N ⧸ I.map (algebraMap R S) • (⊤ : Submodule S N)) ≃ₗ[R]
    S ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  ((tensorQuotEquivQuotSMul N (I.map (algebraMap R S))).restrictScalars R).symm ≪≫ₗ
    hf.tensorEquiv R S M _ ≪≫ₗ  LinearEquiv.lTensor M (I.qoutMapEquivTensorQout S) ≪≫ₗ
      leftComm R M S _ ≪≫ₗ LinearEquiv.lTensor S (tensorQuotEquivQuotSMul M I)

theorem Module.FaithfullyFlat.smul_top_ne_top_of_isBaseChange {I : Ideal R}
    (h : I • (⊤ : Submodule R M) ≠ ⊤) : I.map (algebraMap R S) • (⊤ : Submodule S N) ≠ ⊤ := by
  intro eq
  have := Submodule.subsingleton_quotient_iff_eq_top.mpr eq
  have := (hf.quotMapSMulEquivTensorQuot I).symm.subsingleton
  have : Subsingleton (M ⧸ (I • (⊤ : Submodule R M))) := lTensor_reflects_triviality R S _
  exact not_nontrivial _ (Submodule.Quotient.nontrivial_of_lt_top (I • ⊤) h.lt_top)

end FaithfullyFlat
