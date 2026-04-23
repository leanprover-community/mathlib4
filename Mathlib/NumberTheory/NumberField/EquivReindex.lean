/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Matrix.Invertible
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.RingTheory.Discriminant
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# Reindexed basis
This file introduces an equivalence between the set of embeddings of `K` into `ℂ` and the
index set of the chosen basis of the ring of integers of `K`.

## Tags

house, number field, algebraic number
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

/-- An equivalence between the set of embeddings of `K` into `ℂ` and the
  index set of the chosen basis of the ring of integers of `K`. -/
abbrev equivReindex : (K →+* ℂ) ≃ ChooseBasisIndex ℤ (𝓞 K) :=
  Fintype.equivOfCardEq <| by
    rw [Embeddings.card, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

/-- The basis matrix for the embeddings of `K` into `ℂ`. This matrix is formed by
  taking the lattice basis vectors of `K` and reindexing them according to the
  equivalence `equivReindex`, then transposing the resulting matrix. -/
abbrev basisMatrix : Matrix (K →+* ℂ) (K →+* ℂ) ℂ :=
  (Matrix.of fun i ↦ latticeBasis K (equivReindex K i))

theorem basisMatrix_eq_embeddingsMatrixReindex :
    basisMatrix K = Algebra.embeddingsMatrixReindex ℚ ℂ
      (integralBasis K ∘ (equivReindex K)) RingHom.equivRatAlgHom := by
  ext; simp [Algebra.embeddingsMatrixReindex]

open ComplexConjugate in
theorem conj_basisMatrix :
    (basisMatrix K).map conj = (basisMatrix K).reindex (Equiv.refl _)
      (ComplexEmbedding.involutive_conjugate K).toPerm := by
  ext; simp

theorem det_of_basisMatrix_non_zero [DecidableEq (K →+* ℂ)] : (basisMatrix K).det ≠ 0 := by
  rw [basisMatrix_eq_embeddingsMatrixReindex, ← pow_ne_zero_iff two_ne_zero]
  convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
    (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
  rw [← Algebra.discr_reindex ℚ (integralBasis K) (equivReindex K).symm]
  exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
    (integralBasis K ∘ (equivReindex K)) RingHom.equivRatAlgHom).symm

instance [DecidableEq (K →+* ℂ)] : Invertible (basisMatrix K) := invertibleOfIsUnitDet _
    (Ne.isUnit (det_of_basisMatrix_non_zero K))

variable {K}

theorem canonicalEmbedding_eq_basisMatrix_mulVec (α : K) :
    canonicalEmbedding K α = (basisMatrix K).transpose.mulVec
      (fun i ↦ (((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)) := by
  ext i
  rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α), ← Equiv.sum_comp (equivReindex K)]
  simp only [canonicalEmbedding.integralBasis_repr_apply, mulVec, dotProduct,
    transpose_apply, of_apply, Fintype.sum_apply, mul_comm, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Pi.smul_apply, smul_eq_mul]

theorem inverse_basisMatrix_mulVec_eq_repr [DecidableEq (K →+* ℂ)] (α : 𝓞 K) :
    ∀ i, ((basisMatrix K).transpose)⁻¹.mulVec (fun j =>
      canonicalEmbedding K (algebraMap (𝓞 K) K α) j) i =
      ((integralBasis K).reindex (equivReindex K).symm).repr α i := fun i => by
  rw [inv_mulVec_eq_vec (canonicalEmbedding_eq_basisMatrix_mulVec ((algebraMap (𝓞 K) K) α))]

end

end NumberField
