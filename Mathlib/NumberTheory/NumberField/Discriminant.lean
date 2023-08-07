/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Number field discriminant
This file defines the discrimiant of a number field.

-/

namespace NumberField

open NumberField Matrix

variable (K : Type _) [Field K] [NumberField K]

/-- The discriminant of a number field. -/
noncomputable def discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)

theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) := by
  rw [discr]
  exact (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm

theorem discr_ne_zero : discr K ≠ 0 := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, coe_discr]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

theorem discr_eq_discr {ι : Type _} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀, discr, Basis.coe_reindex, Algebra.discr_reindex]

end NumberField

namespace Rat

open NumberField

theorem discr : discr ℚ = 1 := by
  let b : Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Basis.map (Basis.singleton (Fin 1) ℤ) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr ℚ
    _ = Algebra.discr ℤ b := by convert (discr_eq_discr ℚ b).symm
    _ = Matrix.det (Algebra.traceMatrix ℤ b) := rfl
    _ = Algebra.trace ℤ (𝓞 ℚ) 1 := ?_
    _ = 1                 := by rw [Algebra.trace_eq_matrix_trace b]; norm_num
  rw [Matrix.det_unique, Algebra.traceMatrix_apply, Basis.map_apply, Basis.singleton_apply,
    AddEquiv.toIntLinearEquiv_symm, AddEquiv.coe_toIntLinearEquiv, RingEquiv.toAddEquiv_eq_coe,
    show (AddEquiv.symm ringOfIntegersEquiv) (1 : ℤ) = (1 : 𝓞 ℚ) by
      rw [AddEquiv.symm_apply_eq, RingEquiv.coe_toAddEquiv, map_one],
    Algebra.traceForm_apply, mul_one]

end Rat
