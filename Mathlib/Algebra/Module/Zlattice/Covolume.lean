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

-/

noncomputable section

namespace Zlattice

open Submodule MeasureTheory FiniteDimensional MeasureTheory

section General

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] [MeasurableSpace E] {L : AddSubgroup E} [DiscreteTopology L]
variable (hs : span K (L : Set E) = ⊤)

/-- The covolume of a `ℤ`-lattice is the volume of a fundamental domain; see
`Zlattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ :=
  (μ (Zspan.fundamentalDomain (basis K hs))).toReal

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {L : AddSubgroup E} [DiscreteTopology L] (hs : span ℝ (L : Set E) = ⊤)
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_ne_zero : covolume ℝ hs μ ≠ 0 := by
  rw [covolume, ENNReal.toReal_ne_zero]
  refine ⟨Zspan.measure_fundamentalDomain_ne_zero (basis ℝ hs), ne_of_lt ?_⟩
  exact Bornology.IsBounded.measure_lt_top (Zspan.fundamentalDomain_isBounded (basis ℝ hs))

theorem covolume_pos : 0 < covolume ℝ hs μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero hs μ).symm

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume ℝ hs μ = (μ F).toReal := by
  have : Countable L := by
    rw [← Zlattice.basis_span ℝ hs]
    change Countable (span ℤ (Set.range (basis ℝ hs)))
    infer_instance
  refine congr_arg ENNReal.toReal (IsAddFundamentalDomain.measure_eq ?_ h)
  convert (Zlattice.basis_span ℝ hs) ▸ (Zspan.isAddFundamentalDomain (basis ℝ hs) μ)

theorem covolume_eq_det_mul_measure {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι ℝ E}
    (hb : (span ℤ (Set.range b)).toAddSubgroup = L) (b₀ : Basis ι ℝ E) :
    covolume ℝ hs μ = |b₀.det b| * (μ (Zspan.fundamentalDomain b₀)).toReal := by
  rw [covolume_eq_measure_fundamentalDomain hs μ (hb ▸ Zspan.isAddFundamentalDomain b μ),
    Zspan.measure_fundamentalDomain _ _ b₀, measure_congr
    (Zspan.fundamentalDomain_ae_parallelepiped b₀ μ), ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (by positivity)]

theorem covolume_pi_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι ℝ (ι → ℝ)}
    {L : AddSubgroup (ι → ℝ)} [DiscreteTopology L] (hs : span ℝ (L : Set (ι → ℝ)) = ⊤)
    (hb : (span ℤ (Set.range b)).toAddSubgroup = L) :
    covolume ℝ hs = |(Matrix.of b).det| := by
  rw [covolume_eq_measure_fundamentalDomain hs volume (hb ▸ Zspan.isAddFundamentalDomain b volume),
    Zspan.volume_fundamentalDomain, ENNReal.toReal_ofReal (by positivity)]

end Real

end Zlattice
