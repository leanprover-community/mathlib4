/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Basic

/-!
# Covolume of ℤ-lattices

Let `E` be a finite dimensional real vector space with an inner product.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `AddSubgroup E` that spans `E` over `ℝ`.

## Main definitions and results

* `Zlattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
domain of `L`.

* `Zlattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
choice of the fundamental domain of `L`.

* `Zlattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
value of the determinant of any `ℤ`-basis of `L`.

-/

noncomputable section

namespace Zlattice

open Submodule MeasureTheory FiniteDimensional MeasureTheory Module

section General

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] [MeasurableSpace E]
variable (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice K L]

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`Zlattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = (μ F).toReal := congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    ENNReal.toReal_ne_zero]
  refine ⟨Zspan.measure_fundamentalDomain_ne_zero _, ne_of_lt ?_⟩
  exact Bornology.IsBounded.measure_lt_top (Zspan.fundamentalDomain_isBounded _)

theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

theorem covolume_eq_det_mul_measure {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * (μ (Zspan.fundamentalDomain b₀)).toReal := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    Zspan.measure_fundamentalDomain _ _ b₀, measure_congr
    (Zspan.fundamentalDomain_ae_parallelepiped b₀ μ), ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (by positivity)]
  congr
  ext
  exact b.ofZlatticeBasis_apply ℝ L _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : AddSubgroup (ι → ℝ))
    [DiscreteTopology L] [IsZlattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    Zspan.volume_fundamentalDomain, ENNReal.toReal_ofReal (by positivity)]
  congr
  ext1
  exact b.ofZlatticeBasis_apply ℝ L _

end Real

end Zlattice
