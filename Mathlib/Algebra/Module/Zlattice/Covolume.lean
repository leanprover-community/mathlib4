/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

section general

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] [MeasureSpace E] {L : AddSubgroup E} [DiscreteTopology L]
variable (hs : span K (L : Set E) = ⊤)

/-- The covolume of a `ℤ`-lattice is the volume of a fundamental domain; see
`Zlattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume : ℝ := (volume (Zspan.fundamentalDomain (basis K hs))).toReal

end general

section Innerproductspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {L : AddSubgroup E} [DiscreteTopology L] (hs : span ℝ (L : Set E) = ⊤)

theorem covolume_ne_zero : covolume ℝ hs ≠ 0 := by
  rw [covolume, ENNReal.toReal_ne_zero]
  refine ⟨Zspan.measure_fundamentalDomain_ne_zero (basis ℝ hs), ne_of_lt ?_⟩
  exact Bornology.IsBounded.measure_lt_top (Zspan.fundamentalDomain_isBounded (basis ℝ hs))

theorem covolume_pos : 0 < covolume ℝ hs :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero hs).symm

theorem covolume_eq_volume {F : Set E} (h : IsAddFundamentalDomain L F) :
    covolume ℝ hs = (volume F).toReal := by
  have : Countable L := by
    rw [← Zlattice.basis_span ℝ hs]
    change Countable (span ℤ (Set.range (basis ℝ hs)))
    infer_instance
  refine congr_arg ENNReal.toReal (IsAddFundamentalDomain.measure_eq ?_ h)
  convert (Zlattice.basis_span ℝ hs) ▸ (Zspan.isAddFundamentalDomain (basis ℝ hs) volume)

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι ℝ E}
    (hb : (span ℤ (Set.range b)).toAddSubgroup = L) (B : OrthonormalBasis ι ℝ E) :
    covolume ℝ hs = |B.toBasis.det b| := by
  rw [covolume_eq_volume hs (hb ▸ Zspan.isAddFundamentalDomain b volume),
    Zspan.measure_fundamentalDomain _ _ B.toBasis, measure_congr
    (Zspan.fundamentalDomain_ae_parallelepiped B.toBasis volume), OrthonormalBasis.coe_toBasis,
    B.volume_parallelepiped, mul_one, ENNReal.toReal_ofReal (by positivity)]

end Innerproductspace

end Zlattice
