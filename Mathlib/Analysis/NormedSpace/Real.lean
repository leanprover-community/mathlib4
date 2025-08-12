/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Eric Wieser, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Basic facts about real (semi)normed spaces

In this file we prove some theorems about (semi)normed spaces over real numberes.

## Main results

- `closure_ball`, `frontier_ball`, `interior_closedBall`, `frontier_closedBall`, `interior_sphere`,
  `frontier_sphere`: formulas for the closure/interior/frontier
  of nontrivial balls and spheres in a real seminormed space;

- `interior_closedBall'`, `frontier_closedBall'`, `interior_sphere'`, `frontier_sphere'`:
  similar lemmas assuming that the ambient space is separated and nontrivial instead of `r ≠ 0`.
-/

open Metric Set Function Filter
open scoped NNReal Topology

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `Module.punctured_nhds_neBot`. -/
instance Real.punctured_nhds_module_neBot {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousAdd E] [Nontrivial E] [Module ℝ E] [ContinuousSMul ℝ E] (x : E) : NeBot (𝓝[≠] x) :=
  Module.punctured_nhds_neBot ℝ E x

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_norm_smul_mem_unitClosedBall (x : E) :
    ‖x‖⁻¹ • x ∈ closedBall (0 : E) 1 := by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    div_self_le_one]

theorem norm_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖t • x‖ = t * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

theorem dist_smul_add_one_sub_smul_le {r : ℝ} {x y : E} (h : r ∈ Icc 0 1) :
    dist (r • x + (1 - r) • y) x ≤ dist y x :=
  calc
    dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ := by
      simp_rw [dist_eq_norm', ← norm_smul, sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add,
        sub_right_comm]
    _ = (1 - r) * dist y x := by
      rw [Real.norm_eq_abs, abs_eq_self.mpr (sub_nonneg.mpr h.2), dist_eq_norm']
    _ ≤ (1 - 0) * dist y x := by gcongr; exact h.1
    _ = dist y x := by rw [sub_zero, one_mul]

theorem closure_ball (x : E) {r : ℝ} (hr : r ≠ 0) : closure (ball x r) = closedBall x r := by
  refine Subset.antisymm closure_ball_subset_closedBall fun y hy => ?_
  have : ContinuousWithinAt (fun c : ℝ => c • (y - x) + x) (Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuousWithinAt
  convert this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm, ← mul_one r]
    rw [mem_closedBall, dist_eq_norm] at hy
    replace hr : 0 < r := ((norm_nonneg _).trans hy).lt_of_ne hr.symm
    apply mul_lt_mul' <;> assumption

theorem frontier_ball (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (ball x r) = sphere x r := by
  rw [frontier, closure_ball x hr, isOpen_ball.interior_eq, closedBall_diff_ball]

theorem interior_closedBall (x : E) {r : ℝ} (hr : r ≠ 0) :
    interior (closedBall x r) = ball x r := by
  rcases hr.lt_or_gt with hr | hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine Subset.antisymm ?_ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : ℝ → E := fun c : ℝ => c • (y - x) + x
  suffices f ⁻¹' closedBall x (dist y x) ⊆ Icc (-1) 1 by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' interior (closedBall x <| dist y x) := by simpa [f]
    have h1 : (1 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    simp at h1
  intro c hc
  rw [mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [f, dist_eq_norm, norm_smul] using hc

theorem frontier_closedBall (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall x hr, closedBall_diff_ball]

theorem interior_sphere (x : E) {r : ℝ} (hr : r ≠ 0) : interior (sphere x r) = ∅ := by
  rw [← frontier_closedBall x hr, interior_frontier isClosed_closedBall]

theorem frontier_sphere (x : E) {r : ℝ} (hr : r ≠ 0) : frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq, interior_sphere x hr, diff_empty]

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

section Surj

variable (E)

theorem exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rw [← norm_ne_zero_iff] at hx
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, inv_mul_cancel₀ hx]

@[simp]
theorem range_norm : range (norm : E → ℝ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E

theorem nnnorm_surjective : Surjective (nnnorm : E → ℝ≥0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h

@[simp]
theorem range_nnnorm : range (nnnorm : E → ℝ≥0) = univ :=
  (nnnorm_surjective E).range_eq

variable {E} in
/-- In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp]
theorem NormedSpace.sphere_nonempty {x : E} {r : ℝ} : (sphere x r).Nonempty ↔ 0 ≤ r := by
  refine ⟨fun h => nonempty_closedBall.1 (h.mono sphere_subset_closedBall), fun hr => ?_⟩
  obtain ⟨y, hy⟩ := exists_norm_eq E hr
  exact ⟨x + y, by simpa using hy⟩

end Surj

theorem interior_closedBall' (x : E) (r : ℝ) : interior (closedBall x r) = ball x r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr

theorem frontier_closedBall' (x : E) (r : ℝ) : frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall' x r, closedBall_diff_ball]

@[simp]
theorem interior_sphere' (x : E) (r : ℝ) : interior (sphere x r) = ∅ := by
  rw [← frontier_closedBall' x, interior_frontier isClosed_closedBall]

@[simp]
theorem frontier_sphere' (x : E) (r : ℝ) : frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq, interior_sphere' x, diff_empty]

end Normed
