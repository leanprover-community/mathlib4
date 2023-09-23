/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Number field discriminant
This file defines the discriminant of a number field.

## Main definitions
 - `discr` the absolute discriminant of a number field.

## Tags
number field, discriminant
-/

-- TODO. Rewrite some of the FLT results on the disciminant using the definitions and results of
-- this file

namespace NumberField

open Classical NumberField Matrix

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant of a number field. -/
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)

theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) :=
  (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm

theorem discr_ne_zero : discr K ≠ 0 := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, coe_discr]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀, Basis.coe_reindex, Algebra.discr_reindex]

open MeasureTheory MeasureTheory.Measure Zspan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ℝ≥0)⁻¹ ^ Fintype.card { w : InfinitePlace K // IsComplex w } *
        Real.toNNReal (Real.sqrt |discr K|) := by
  rw [← toNNReal_eq_toNNReal_iff' (ne_of_lt (fundamentalDomain_isBounded _).measure_lt_top)
    (ENNReal.mul_ne_top (coe_ne_top) (coe_ne_top)), toNNReal_mul, toNNReal_coe]
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun ℂ _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)
  let N := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K ∘ f.symm)
    RingHom.equivRatAlgHom
  suffices M.map Complex.ofReal = (matrix_to_stdBasis K) *
      (Matrix.reindex (indexEquiv K).symm (indexEquiv K).symm N).transpose by
    calc
      _ = Real.toNNReal (|((mixedEmbedding.stdBasis K).toMatrix
            ((latticeBasis K).reindex e.symm)).det|) := by
        rw [← fundamentalDomain_reindex _ e.symm, measure_fundamentalDomain
          ((latticeBasis K).reindex e.symm), volume_fundamentalDomain_stdBasis, mul_one]
        rfl
      _ = Real.toNNReal (Complex.abs ((matrix_to_stdBasis K).det * N.det)) := by
        rw [← Complex.abs_ofReal, ← Complex.ofReal_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply,
          this, Matrix.det_mul, Matrix.det_transpose, Matrix.det_reindex_self]
      _ = (2 : ℝ≥0)⁻¹ ^ Fintype.card {w // IsComplex w} * Real.toNNReal (Complex.abs N.det) := by
        rw [_root_.map_mul, det_matrix_to_stdBasis, Real.toNNReal_mul (Complex.abs.nonneg _),
          Complex.abs_pow, _root_.map_mul, Complex.abs_I, mul_one, map_inv₀, Complex.abs_two,
          Real.toNNReal_pow (by norm_num), Real.toNNReal_inv, Real.toNNReal_ofNat]
      _ = (2 : ℝ≥0)⁻¹ ^ Fintype.card {w : InfinitePlace K // IsComplex w} *
            Real.toNNReal (Real.sqrt (Complex.abs (N.det ^ 2))) := by
        rw [Complex.abs_pow, Real.sqrt_sq (Complex.abs.nonneg _)]
      _ = (2 : ℝ≥0)⁻¹ ^ Fintype.card { w // IsComplex w } *
            Real.toNNReal (Real.sqrt |(discr K)|) := by
        rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_reindex,
          ← coe_discr, map_intCast, Complex.int_cast_abs]
  ext : 2
  dsimp only
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.coe_reindex, Function.comp, Equiv.symm_symm,
    latticeBasis_apply, ← commMap_canonical_eq_mixed, Complex.ofReal_eq_coe,
    stdBasis_repr_eq_matrix_to_stdBasis_mul K _ (fun _ => rfl)]
  rfl

end NumberField

namespace Rat

open NumberField

/-- The absolute discriminant of the number field `ℚ` is 1. -/
@[simp]
theorem numberField_discr : discr ℚ = 1 := by
  let b : Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Basis.map (Basis.singleton (Fin 1) ℤ) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr ℚ
    _ = Algebra.discr ℤ b := by convert (discr_eq_discr ℚ b).symm
    _ = Algebra.trace ℤ (𝓞 ℚ) (b default * b default) := by
      rw [Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    _ = Algebra.trace ℤ (𝓞 ℚ) 1 := by
      rw [Basis.map_apply, RingEquiv.toAddEquiv_eq_coe, AddEquiv.toIntLinearEquiv_symm,
        AddEquiv.coe_toIntLinearEquiv, Basis.singleton_apply,
        show (AddEquiv.symm ↑ringOfIntegersEquiv) (1 : ℤ) = ringOfIntegersEquiv.symm 1 by rfl,
        map_one, mul_one]
    _ = 1 := by rw [Algebra.trace_eq_matrix_trace b]; norm_num

alias _root_.NumberField.discr_rat := numberField_discr

end Rat
