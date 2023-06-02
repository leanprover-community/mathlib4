/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module number_theory.liouville.residual
! leanprover-community/mathlib commit 32b08ef840dd25ca2e47e035c5da03ce16d2dc3c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.Liouville.Basic
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Topology.Instances.Irrational

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/


open scoped Filter

open Filter Set Metric

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
theorem setOf_liouville_eq_iInter_iUnion :
    { x | Liouville x } =
      ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (hb : 1 < b), ball (a / b) (1 / b ^ n) \ {a / b} := by
  ext x
  simp only [mem_Inter, mem_Union, Liouville, mem_set_of_eq, exists_prop, mem_diff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm']
#align set_of_liouville_eq_Inter_Union setOf_liouville_eq_iInter_iUnion

theorem isGδ_setOf_liouville : IsGδ { x | Liouville x } := by
  rw [setOf_liouville_eq_iInter_iUnion]
  refine' isGδ_iInter fun n => IsOpen.isGδ _
  refine' isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun hb => _
  exact is_open_ball.inter is_closed_singleton.is_open_compl
#align is_Gδ_set_of_liouville isGδ_setOf_liouville

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
theorem setOf_liouville_eq_irrational_inter_iInter_iUnion :
    { x | Liouville x } =
      { x | Irrational x } ∩ ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (hb : 1 < b), ball (a / b) (1 / b ^ n) := by
  refine' subset.antisymm _ _
  · refine' subset_inter (fun x hx => hx.Irrational) _
    rw [setOf_liouville_eq_iInter_iUnion]
    exact Inter_mono fun n => Union₂_mono fun a b => Union_mono fun hb => diff_subset _ _
  · simp only [inter_Inter, inter_Union, setOf_liouville_eq_iInter_iUnion]
    refine' Inter_mono fun n => Union₂_mono fun a b => Union_mono fun hb => _
    rw [inter_comm]
    refine' diff_subset_diff subset.rfl (singleton_subset_iff.2 ⟨a / b, _⟩)
    norm_cast
#align set_of_liouville_eq_irrational_inter_Inter_Union setOf_liouville_eq_irrational_inter_iInter_iUnion

/-- The set of Liouville numbers is a residual set. -/
theorem eventually_residual_liouville : ∀ᶠ x in residual ℝ, Liouville x := by
  rw [Filter.Eventually, setOf_liouville_eq_irrational_inter_iInter_iUnion]
  refine' eventually_residual_irrational.and _
  refine' eventually_residual.2 ⟨_, _, rat.dense_embedding_coe_real.dense.mono _, subset.rfl⟩
  ·
    exact
      isGδ_iInter fun n =>
        IsOpen.isGδ <|
          isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun hb => is_open_ball
  · rintro _ ⟨r, rfl⟩
    simp only [mem_Inter, mem_Union]
    refine' fun n => ⟨r.num * 2, r.denom * 2, _, _⟩
    · have := Int.ofNat_le.2 r.pos; rw [Int.ofNat_one] at this ; linarith
    · convert mem_ball_self _ using 2
      · push_cast ; norm_cast; norm_num
      · refine' one_div_pos.2 (pow_pos (Int.cast_pos.2 _) _)
        exact mul_pos (Int.coe_nat_pos.2 r.pos) zero_lt_two
#align eventually_residual_liouville eventually_residual_liouville

/-- The set of Liouville numbers in dense. -/
theorem dense_liouville : Dense { x | Liouville x } :=
  dense_of_mem_residual eventually_residual_liouville
#align dense_liouville dense_liouville

