/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Euclidean distance on a finite-dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `toEuclidean` to be
an equivalence between a finite-dimensional topological vector space and the standard Euclidean
space of the same dimension.
Then we define `Euclidean.dist x y = dist (toEuclidean x) (toEuclidean y)` and
provide some definitions (`Euclidean.ball`, `Euclidean.closedBall`) and simple lemmas about this
distance. This way we hide the usage of `toEuclidean` behind an API.
-/

@[expose] public section


open scoped Topology

open Set

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable section

open Module

/-- If `E` is a finite-dimensional space over `ℝ`, then `toEuclidean` is a continuous `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension. -/
def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin <| finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

namespace Euclidean

/-- If `x` and `y` are two points in a finite-dimensional space over `ℝ`, then `Euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
nonrec def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)

/-- Closed ball w.r.t. the Euclidean distance. -/
def closedBall (x : E) (r : ℝ) : Set E :=
  {y | dist y x ≤ r}

/-- Open ball w.r.t. the Euclidean distance. -/
def ball (x : E) (r : ℝ) : Set E :=
  {y | dist y x < r}

theorem ball_eq_preimage (x : E) (r : ℝ) :
    ball x r = toEuclidean ⁻¹' Metric.ball (toEuclidean x) r :=
  rfl

theorem closedBall_eq_preimage (x : E) (r : ℝ) :
    closedBall x r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean x) r :=
  rfl

theorem ball_subset_closedBall {x : E} {r : ℝ} : ball x r ⊆ closedBall x r := fun _ (hy : _ < r) =>
  le_of_lt hy

@[simp] theorem isOpen_ball {x : E} {r : ℝ} : IsOpen (ball x r) :=
  Metric.isOpen_ball.preimage toEuclidean.continuous

theorem mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ ball x r :=
  Metric.mem_ball_self hr

theorem closedBall_eq_image (x : E) (r : ℝ) :
    closedBall x r = toEuclidean.symm '' Metric.closedBall (toEuclidean x) r := by
  rw [toEuclidean.image_symm_eq_preimage, closedBall_eq_preimage]

nonrec theorem isCompact_closedBall {x : E} {r : ℝ} : IsCompact (closedBall x r) := by
  rw [closedBall_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous

theorem isClosed_closedBall {x : E} {r : ℝ} : IsClosed (closedBall x r) :=
  isCompact_closedBall.isClosed

nonrec theorem closure_ball (x : E) {r : ℝ} (h : r ≠ 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage, ← toEuclidean.preimage_closure, closure_ball (toEuclidean x) h,
    closedBall_eq_preimage]

nonrec theorem exists_pos_lt_subset_ball {R : ℝ} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s)
    (h : s ⊆ ball x R) : ∃ r ∈ Ioo 0 R, s ⊆ ball x r := by
  rw [ball_eq_preimage, ← image_subset_iff] at h
  rcases exists_pos_lt_subset_ball hR (toEuclidean.isClosed_image.2 hs) h with ⟨r, hr, hsr⟩
  exact ⟨r, hr, image_subset_iff.1 hsr⟩

theorem nhds_basis_closedBall {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (closedBall x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_closedBall.comap _

theorem closedBall_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : closedBall x r ∈ 𝓝 x :=
  nhds_basis_closedBall.mem_of_mem hr

theorem nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (ball x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_ball.comap _

theorem ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ball x r ∈ 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr

end Euclidean

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [NormedAddCommGroup G]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f g : F → G} {n : ℕ∞}

theorem ContDiff.euclidean_dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun x => Euclidean.dist (f x) (g x) := by
  simp only [Euclidean.dist]
  apply ContDiff.dist ℝ
  exacts [(toEuclidean (E := G)).contDiff.comp hf,
    (toEuclidean (E := G)).contDiff.comp hg, fun x => toEuclidean.injective.ne (h x)]

lemma image_closedBall_eq_metric_closedBall [Nontrivial G] (x : G) (r : ℝ) :
  toEuclidean '' Euclidean.closedBall x r = Metric.closedBall (toEuclidean x) r := by
  simp only [Euclidean.closedBall, Euclidean.dist]
  apply Set.eq_of_subset_of_subset
  · rw [image_subset_iff]
    rfl
  · intro y hy
    refine ⟨(toEuclidean.symm y), ?_, ?_⟩
    · simp_all [Metric.mem_closedBall, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply]
    · apply ContinuousLinearEquiv.apply_symm_apply

lemma diam_closed_ball_eq_two_mul_radius' [Nontrivial G] (x : G) (r : ℝ) (hr : 0 ≤ r) :
  Metric.diam (Metric.closedBall (toEuclidean x) r) = 2 * r := by
  apply le_antisymm (Metric.diam_closedBall hr)
  let x₁ := (toEuclidean x) + EuclideanSpace.single ⟨0, Module.finrank_pos⟩ r
  let x₂ := (toEuclidean x) - EuclideanSpace.single ⟨0, Module.finrank_pos⟩ r
  refine le_trans ?_ (Metric.dist_le_diam_of_mem (x := x₁) (y := x₂) ?_ ?_ ?_)
  rotate_left
  · exact Metric.isBounded_closedBall
  · rw [Metric.mem_closedBall, dist_self_add_left,
      EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_nonneg hr]
  · simp only [Metric.mem_closedBall, dist_self_sub_left, EuclideanSpace.norm_eq,
      EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hr,
      Real.sqrt_sq, le_refl, x₂]
  · norm_num [dist_eq_norm, EuclideanSpace.norm_eq]
    rw [Finset.sum_eq_single ⟨0, Module.finrank_pos⟩]
    · simp_all only [PiLp.add_apply, EuclideanSpace.single_apply, ↓reduceIte, PiLp.sub_apply,
        add_sub_sub_cancel, nonneg_add_self_iff, Real.sqrt_sq, x₁, x₂]
      linarith
    · intro b _ hnb
      simp only [PiLp.add_apply, EuclideanSpace.single_apply, hnb, ↓reduceIte, add_zero,
        PiLp.sub_apply, sub_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, x₁, x₂]
    · simp only [Finset.mem_univ, not_true_eq_false, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, IsEmpty.forall_iff]

/-- The diameter of a closed Euclidean ball is twice its radius. -/
theorem diam_closed_ball_eq_two_mul_radius [Nontrivial G] (x : G) (r : ℝ) (hr : 0 ≤ r) :
  Metric.diam (toEuclidean '' (Euclidean.closedBall x r)) = 2 * r := by
  rw [image_closedBall_eq_metric_closedBall, diam_closed_ball_eq_two_mul_radius' x r hr]

/-- The diameter of an open Euclidean ball is twice its radius. -/
theorem diam_ball_eq_two_mul_radius [Nontrivial G] (x : G) (r : ℝ) (hr : 0 ≤ r) :
    Metric.diam (toEuclidean '' (Euclidean.ball x r)) = 2 * r := by
  simp only [Euclidean.ball_eq_preimage, image_preimage_eq_inter_range, EquivLike.range_eq_univ,
    inter_univ, ← diam_closed_ball_eq_two_mul_radius x r hr, Euclidean.closedBall_eq_preimage]
  by_cases hr : r = 0
  · simp only [hr, Metric.ball_zero, Metric.diam_empty, Metric.closedBall_zero,
    Metric.diam_singleton]
  · rw [Metric.diam, Metric.diam, ←_root_.closure_ball _ hr, EMetric.diam_closure]
