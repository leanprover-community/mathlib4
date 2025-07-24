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

variable [FiniteDimensional K L]

private theorem exists_linearIndependent_algEquiv_apply_of_infinite [Infinite K] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  classical
  have e := Module.Free.chooseBasis K L
  let M : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (MvPolynomial _ L) :=
    .of fun i j ↦ ∑ k, i.symm (j (e k)) • .X k
  have hM : M.det ≠ 0 := by
    have hq : Submodule.span L (Set.range fun i (j : L ≃ₐ[K] L) ↦ j (e i)) = ⊤ := by
      apply span_flip_eq_top_iff_linearIndependent.mpr <|
        ((linearIndependent_algHom_toLinearMap K L L).comp _
          (algEquivEquivAlgHom K L).injective).map' _ (e.constr L).symm.ker
    obtain ⟨c, hc⟩ : ∃ c : _ → L, M.det.eval c = 1 := by
      have h := (congr_arg (fun s ↦ Pi.single 1 1 ∈ s) hq).mpr (Submodule.mem_top ..)
      rw [← Set.image_univ, ← Finset.coe_univ,
        ← Function.Embedding.coeFn_mk (fun i (j : L ≃ₐ[K] L) ↦ j (e i))
          fun a b hab ↦ e.injective (congrFun hab .refl),
        ← Finset.coe_map, Submodule.mem_span_finset'] at h
      obtain ⟨f, hf⟩ := h
      let g k : L := f ⟨fun j ↦ j (e k), Finset.mem_map_of_mem _ (Finset.mem_univ k)⟩
      conv at hf =>
        enter [1, 2, a, 1]
        equals g (Function.invFun (fun i (j : L ≃ₐ[K] L) => j (e i)) a) =>
          apply congr_arg f
          apply Subtype.ext
          symm
          apply Function.invFun_eq (f := fun i (j : L ≃ₐ[K] L) => j (e i))
          exact (Finset.mem_map.1 a.prop).imp fun _ => And.right
      rw [Finset.sum_coe_sort (Finset.map ..)
        fun a ↦ g (Function.invFun _ a) • a, Finset.sum_map] at hf
      conv at hf =>
        enter [1, 2, a, 1]
        equals g a =>
          apply congr_arg f
          apply Subtype.ext
          apply Function.apply_invFun_apply (f := fun i (j : L ≃ₐ[K] L) => j (e i))
      simp_rw [Function.Embedding.coeFn_mk] at hf
      use g
      rw [RingHom.map_det]
      refine (congr_arg Matrix.det ?_).trans Matrix.det_one
      ext i j
      simpa [M, Pi.single_apply, inv_mul_eq_one, mul_comm, Matrix.one_apply]
        using congrFun hf (i⁻¹ * j)
    have : Infinite L := .of_injective (algebraMap K L) (algebraMap K L).injective
    rw [ne_eq, MvPolynomial.funext_iff, not_forall]
    use c
    simp only [hc, map_zero, one_ne_zero, not_false_eq_true]
  obtain ⟨b, hb⟩ : ∃ b : _ → K, M.det.eval (algebraMap K L ∘ b) ≠ 0 := by
    by_contra! h
    apply hM
    apply MvPolynomial.funext_set fun _ => Set.range (algebraMap K L)
    · exact fun _ => Set.infinite_range_of_injective (algebraMap K L).injective
    · intro x hx
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_range, forall_const] at hx
      choose u hu using hx
      replace hu : algebraMap K L ∘ u = x := funext hu
      subst hu
      simpa using h u
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hb
  use ∑ k, b k • e k
  rw [linearIndependent_iff]
  intro a ha
  refine DFunLike.coe_injective (Function.Injective.comp_left ((algebraMap K L).injective) ?_)
  dsimp
  simp only [map_zero, Function.const_zero]
  apply Matrix.eq_zero_of_mulVec_eq_zero hb
  ext i
  apply i.injective
  unfold M
  simp only [Matrix.mulVec_eq_sum, Function.comp_apply, op_smul_eq_smul, algebraMap_smul,
    Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    map_sum, MvPolynomial.smul_eval, MvPolynomial.eval_X, map_smul, map_mul,
    AlgEquiv.apply_symm_apply, AlgEquiv.commutes, Pi.zero_apply, map_zero]
  rw [← ha, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ fun i => zero_smul K (i _)]
  simp_rw [map_sum, map_smul, Algebra.smul_def, mul_comm]

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
