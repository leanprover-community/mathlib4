/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

#align_import measure_theory.group.geometry_of_numbers from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the set.
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/


namespace MeasureTheory

open ENNReal FiniteDimensional MeasureTheory MeasureTheory.Measure Set

open scoped Pointwise

variable {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

/-- **Blichfeldt's Theorem**. If the volume of the set `s` is larger than the covolume of the
countable subgroup `L` of `E`, then there exist two distinct points `x, y ∈ L` such that `(x + s)`
and `(y + s)` are not disjoint. -/
theorem exists_pair_mem_lattice_not_disjoint_vadd [AddCommGroup L] [Countable L] [AddAction L E]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  contrapose! h
  -- ⊢ ↑↑μ s ≤ ↑↑μ F
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_right _ _)
#align measure_theory.exists_pair_mem_lattice_not_disjoint_vadd MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd

/-- The **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E` whose volume
is large enough compared to the covolume of a lattice `L` of `E`, then it contains a non-zero
lattice point of `L`.  -/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] (fund : IsAddFundamentalDomain L F μ)
    (h : μ F * 2 ^ finrank ℝ E < μ s) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) :
    ∃ (x : _) (_ : x ≠ 0), ((x : L) : E) ∈ s := by
  have h_vol : μ F < μ ((2⁻¹ : ℝ) • s) := by
    rw [addHaar_smul_of_nonneg μ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) s, ←
      mul_lt_mul_right (pow_ne_zero (finrank ℝ E) (two_ne_zero' _)) (pow_ne_top two_ne_top),
      mul_right_comm, ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)⁻¹), ← ofReal_inv_of_pos zero_lt_two]
    norm_num
    rwa [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, one_mul]
  obtain ⟨x, y, hxy, h⟩ :=
    exists_pair_mem_lattice_not_disjoint_vadd fund ((h_conv.smul _).nullMeasurableSet _) h_vol
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := Set.not_disjoint_iff.mp h
  -- ⊢ ∃ x x_1, ↑x ∈ s
  refine' ⟨x - y, sub_ne_zero.2 hxy, _⟩
  -- ⊢ ↑(x - y) ∈ s
  rw [Set.mem_inv_smul_set_iff₀ (two_ne_zero' ℝ)] at hv hw
  -- ⊢ ↑(x - y) ∈ s
  simp_rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm _ w, ← sub_eq_sub_iff_add_eq_add, ←
    AddSubgroup.coe_sub] at hvw
  rw [← hvw, ← inv_smul_smul₀ (two_ne_zero' ℝ) (_ - _), smul_sub, sub_eq_add_neg, smul_add]
  -- ⊢ 2⁻¹ • 2 • w + 2⁻¹ • -(2 • v) ∈ s
  refine' h_conv hw (h_symm _ hv) _ _ _ <;> norm_num
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align measure_theory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure

end MeasureTheory
