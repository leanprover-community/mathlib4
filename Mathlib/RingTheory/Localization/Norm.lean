/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.norm
! leanprover-community/mathlib commit 2e59a6de168f95d16b16d217b808a36290398c0a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Norm

/-!

# Field/algebra norm and localization

This file contains results on the combination of `Algebra.norm` and `IsLocalization`.

## Main results

 * `Algebra.norm_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R`
  if `S` is free as `R`-module

## Tags

field norm, algebra norm, localization

-/


open scoped nonZeroDivisors

variable (R : Type _) {S : Type _} [CommRing R] [CommRing S] [Algebra R S]

variable {Rₘ Sₘ : Type _} [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]

variable (M : Submonoid R)

variable [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

/-- Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` respectively.
Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R` if `S` is free as `R`-module.
-/
theorem Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.norm R a) := by
  cases subsingleton_or_nontrivial R
  · haveI : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp
  let b := Module.Free.chooseBasis R S
  letI := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M Sₘ),
    Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Basis.localizationLocalization_apply, ← _root_.map_mul]
  apply Basis.localizationLocalization_repr_algebraMap
#align algebra.norm_localization Algebra.norm_localization
