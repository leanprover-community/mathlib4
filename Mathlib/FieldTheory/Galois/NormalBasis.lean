/-
Copyright (c) 2025 Madison Crim, Aaron Liu, Justus Springer, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim, Aaron Liu, Justus Springer, Junyan Xu
-/
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.AnnihilatingPolynomial

/-!
# The normal basis theorem

We prove the normal basis theorem:
every finite Galois extension has a basis that is an orbit of the Galois group.
-/

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

--attribute [reducible] AdjoinRoot in
open Polynomial FiniteField Module Submodule LinearMap in
private theorem exists_linearIndependent_algEquiv_apply_of_finite [Finite L] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  have := Finite.of_injective _ (algebraMap K L).injective
  have := Fintype.ofFinite K
  have ⟨x, hx⟩ := exists_ker_toSpanSingleton_eq_annihilator K[X]
    (AEval' (frobeniusAlgHom K L).toLinearMap)
  obtain ⟨x, rfl⟩ := (AEval'.of _).surjective x
  use x
  rw [← span_minpoly_eq_annihilator, minpoly_frobeniusAlgHom, eq_comm] at hx
  have ind := (AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero Module.finrank_pos 1)).basis
    |>.linearIndependent.map' ((AEval'.of _).symm.toLinearMap ∘ₗ (Submodule.subtype _ ∘ₗ
      (quotEquivOfEq _ _ hx ≪≫ₗ quotKerEquivRange _).toLinearMap).restrictScalars K)
    (ker_eq_bot.mpr <| by simpa using EquivLike.injective _)
  rw [← linearIndependent_equiv ((finCongr <| natDegree_X_pow_sub_C (R := K)).trans <|
    .ofBijective _ <| bijective_frobeniusAlgEquivOfAlgebraic_pow K L)]
  convert ind
  ext i
  simp only [Function.comp_apply, AdjoinRoot.powerBasis, AdjoinRoot.powerBasisAux,
    coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, coe_subtype,
    Basis.coe_mk, LinearEquiv.trans_apply]
  erw [quotEquivOfEq_mk, quotKerEquivRange_apply_mk]
  simp [AEval'.X_pow_smul_of, Module.End.coe_pow]
  rfl
