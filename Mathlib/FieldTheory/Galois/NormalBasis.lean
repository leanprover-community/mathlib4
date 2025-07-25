/-
Copyright (c) 2025 Madison Crim, Aaron Liu, Justus Springer, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim, Aaron Liu, Justus Springer, Junyan Xu
-/
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The normal basis theorem

We prove the normal basis theorem `IsGalois.exists_linearIndependent_algEquiv_apply`:
every finite Galois extension has a basis that is an orbit under the Galois group action.
-/

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

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
  rw [← linearIndependent_equiv ((finCongr <| natDegree_X_pow_sub_C (R := K)).trans <|
    .ofBijective _ <| bijective_frobeniusAlgEquivOfAlgebraic_pow K L)]
  convert (AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero Module.finrank_pos 1)).basis.linearIndependent
    |>.map' ((AEval'.of _).symm.toLinearMap ∘ₗ (Submodule.subtype _ ∘ₗ
      (quotEquivOfEq _ _ hx ≪≫ₗ quotKerEquivRange _).toLinearMap).restrictScalars K)
    (ker_eq_bot.mpr <| by simpa using EquivLike.injective _)
  ext i
  simp only [Function.comp_apply, AdjoinRoot.powerBasis, AdjoinRoot.powerBasisAux,
    coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, coe_subtype,
    Basis.coe_mk, LinearEquiv.trans_apply]
  erw [quotEquivOfEq_mk, quotKerEquivRange_apply_mk]
  simp [AEval'.X_pow_smul_of, Module.End.coe_pow]
  rfl

variable [FiniteDimensional K L]

private theorem exists_linearIndependent_algEquiv_apply_of_infinite [Infinite K] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  classical
  have e := Module.Free.chooseBasis K L
  let M : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (MvPolynomial _ L) :=
    .of fun i j ↦ ∑ k, i.symm (j (e k)) • .X k
  have hM : M.det ≠ 0 := fun h0 ↦ by
    have hq : Submodule.span L (Set.range fun i (j : L ≃ₐ[K] L) ↦ j (e i)) = ⊤ := by
      apply span_flip_eq_top_iff_linearIndependent.mpr <|
        ((linearIndependent_algHom_toLinearMap K L L).comp _
          (algEquivEquivAlgHom K L).injective).map' _ (e.constr L).symm.ker
    obtain ⟨c, hc⟩ : ∃ c : _ → L, M.det.eval c = 1 := by
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
        (hq ▸ Submodule.mem_top (x := Pi.single 1 1))
      simp_rw [RingHom.map_det]
      refine ⟨g, congr(Matrix.det $(?_)).trans Matrix.det_one⟩
      ext i j
      simpa [M, Pi.single_apply, inv_mul_eq_one, mul_comm, Matrix.one_apply]
        using congr($hg (i⁻¹ * j))
    simpa [hc] using congr(($h0).eval c)
  obtain ⟨b, hb⟩ : ∃ b : _ → K, M.det.eval (algebraMap K L ∘ b) ≠ 0 := by
    by_contra! h
    refine hM (MvPolynomial.funext_set _
      (fun _ ↦ Set.infinite_range_of_injective (algebraMap K L).injective) fun x hx ↦ ?_)
    obtain ⟨x, rfl⟩ := Set.range_piMap _ ▸ hx
    simpa using h x
  refine ⟨∑ k, b k • e k, Fintype.linearIndependent_iff.mpr fun a ha ↦
    funext_iff.mp <| (algebraMap K L).injective.comp_left ?_⟩
  simp_rw [Function.comp_def, map_zero]
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hb
  refine Matrix.eq_zero_of_mulVec_eq_zero hb (funext fun i ↦ i.injective ?_)
  simp_rw [M, Pi.zero_apply, map_zero, ← ha]
  simp [Algebra.smul_def, Matrix.mulVec_eq_sum, mul_comm]

theorem exists_linearIndependent_algEquiv_apply :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  obtain h | h := finite_or_infinite K
  · have := Module.finite_of_finite K (M := L)
    exact exists_linearIndependent_algEquiv_apply_of_finite K L
  · exact exists_linearIndependent_algEquiv_apply_of_infinite K L

namespace IsGalois

variable [IsGalois K L]

/-- Given a finite Galois extension `L/K`, `normalBasis K L` is a basis of `L` over `K`
that is an orbit under the Galois group action. -/
noncomputable def normalBasis : Basis (L ≃ₐ[K] L) K L :=
  basisOfLinearIndependentOfCardEqFinrank
    (exists_linearIndependent_algEquiv_apply K L).choose_spec
    (card_aut_eq_finrank K L)

variable {K L}

theorem normalBasis_apply (e : L ≃ₐ[K] L) : normalBasis K L e = e (normalBasis K L 1) := by
  rw [normalBasis, coe_basisOfLinearIndependentOfCardEqFinrank, AlgEquiv.one_apply]

end IsGalois
