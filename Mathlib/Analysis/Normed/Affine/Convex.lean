/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.Action.Pointwise.Set
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Closure
import Mathlib.Topology.NhdsSet

/-!
# Simplices in normed affine spaces
We prove the following facts:

* `exists_mem_interior_convexHull_affineBasis` : We can intercalate a simplex between a point and
  one of its neighborhoods.
* `Convex.exists_subset_interior_convexHull_finset_of_isCompact`: We can intercalate a convex
  polytope between a compact convex set and one of its neighborhoods.
-/

public section

variable {E P : Type*}

open AffineBasis Module Metric Set
open scoped Convex Pointwise Topology

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace P] [NormedAddTorsor E P]
variable {s : Set E}

theorem Wbtw.dist_add_dist {x y z : P} (h : Wbtw ℝ x y z) :
    dist x y + dist y z = dist x z := by
  obtain ⟨a, ⟨ha₀, ha₁⟩, rfl⟩ := h
  simp [abs_of_nonneg, ha₀, ha₁, sub_mul]

theorem dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) :
    dist x y + dist y z = dist x z :=
  (mem_segment_iff_wbtw.1 h).dist_add_dist

end SeminormedAddCommGroup

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s t : Set E} {x : E}

/-- We can intercalate a simplex between a point and one of its neighborhoods. -/
lemma exists_mem_interior_convexHull_affineBasis (hs : s ∈ 𝓝 x) :
    ∃ b : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E,
      x ∈ interior (convexHull ℝ (range b)) ∧ convexHull ℝ (range b) ⊆ s := by
  classical
  -- By translating, WLOG `x` is the origin.
  wlog hx : x = 0
  · obtain ⟨b, hb⟩ := this (s := -x +ᵥ s) (by simpa using vadd_mem_nhds_vadd (-x) hs) rfl
    use x +ᵥ b
    simpa [subset_vadd_set_iff, mem_vadd_set_iff_neg_vadd_mem, convexHull_vadd, interior_vadd,
      Pi.vadd_def, -vadd_eq_add, vadd_eq_add (a := -x), ← Set.vadd_set_range] using hb
  subst hx
  -- The strategy is now to find an arbitrary maximal spanning simplex (aka an affine basis)...
  obtain ⟨b⟩ := exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (P := E) (by simp)
  -- ... translate it to contain the origin...
  set c : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := -Finset.univ.centroid ℝ b +ᵥ b
  have hc₀ : 0 ∈ interior (convexHull ℝ (range c) : Set E) := by
    simpa [c, convexHull_vadd, interior_vadd, range_add, Pi.vadd_def, mem_vadd_set_iff_neg_vadd_mem]
      using b.centroid_mem_interior_convexHull
  set cnorm := Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖c i‖)
  have hcnorm : range c ⊆ closedBall 0 (cnorm + 1) := by
    simpa only [cnorm, subset_def, Finset.mem_coe, mem_closedBall, dist_zero_right,
      ← sub_le_iff_le_add, Finset.le_sup'_iff, forall_mem_range] using fun i ↦ ⟨i, by simp⟩
  -- ... and finally scale it to fit inside the neighborhood `s`.
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  set ε' : ℝ := ε / 2 / (cnorm + 1)
  have hc' : 0 < cnorm + 1 := by
    have : 0 ≤ cnorm := Finset.le_sup'_of_le _ (Finset.mem_univ 0) (norm_nonneg _)
    positivity
  have hε' : 0 < ε' := by positivity
  set d : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := Units.mk0 ε' hε'.ne' • c
  have hε₀ : 0 < ε / 2 := by positivity
  have hdnorm : (range d : Set E) ⊆ closedBall 0 (ε / 2) := by
    simp [d, abs_of_nonneg hε'.le, range_subset_iff, norm_smul]
    simpa [ε', hε₀.ne', range_subset_iff, ← mul_div_right_comm (ε / 2), div_le_iff₀ hc', hε₀]
      using hcnorm
  refine ⟨d, ?_, ?_⟩
  · simpa [d, Pi.smul_def, range_smul, interior_smul₀, convexHull_smul, zero_mem_smul_set_iff,
      hε'.ne']
  · calc
      convexHull ℝ (range d) ⊆ closedBall 0 (ε / 2) := convexHull_min hdnorm (convex_closedBall ..)
      _ ⊆ ball 0 ε := closedBall_subset_ball (by linarith)
      _ ⊆ s := hεs

/-- We can intercalate a convex polytope between a compact convex set and one of its neighborhoods.
-/
theorem Convex.exists_subset_interior_convexHull_finset_of_isCompact
    (hs₁ : Convex ℝ s) (hs₂ : IsCompact s) (ht : t ∈ 𝓝ˢ s) :
    ∃ u : Finset E, s ⊆ interior (convexHull ℝ u) ∧ convexHull ℝ u ⊆ t := by
  classical
  rcases mem_nhdsSet_iff_exists.1 ht with ⟨U, hU₁, hU₂, hU₃⟩
  rcases compact_open_separated_add_left hs₂ hU₁ hU₂ with ⟨V, hV₁, hV₂⟩
  rcases exists_mem_interior_convexHull_affineBasis hV₁ with ⟨b, hb₁, hb₂⟩
  rcases hs₂.elim_finite_subcover_image (b := s)
      (c := fun x => interior (convexHull ℝ (Set.range b)) + {x})
      (fun _ _ => isOpen_interior.add_right)
      (fun x hx => Set.mem_iUnion₂_of_mem hx <| by simpa using hb₁)
    with ⟨u, hu₁, hu₂, hu₃⟩
  lift u to Finset E using hu₂
  refine ⟨Finset.univ.image b + u, ?_, ?_⟩
  all_goals rw [Finset.coe_add, Finset.coe_image, Finset.coe_univ, Set.image_univ, convexHull_add]
  · grw [hu₃, ← subset_interior_add_left, Set.iUnion₂_subset_iff, ← subset_convexHull _ (u : Set E)]
    intros
    gcongr
    simpa
  · grw [hu₁, hs₁.convexHull_eq, hb₂, hV₂, hU₃]

end NormedAddCommGroup
