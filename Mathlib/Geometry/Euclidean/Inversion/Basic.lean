/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.InnerProductSpace.Basic

#align_import geometry.euclidean.inversion from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Inversion in an affine space

In this file we define inversion in a sphere in an affine space. This map sends each point `x` to
the point `y` such that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center
and the radius the sphere.

In many applications, it is convenient to assume that the inversions swaps the center and the point
at infinity. In order to stay in the original affine space, we define the map so that it sends
center to itself.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`.
-/

set_option autoImplicit true

noncomputable section

open Metric Function AffineMap Set AffineSubspace
open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace EuclideanGeometry

variable {a b c d x y z : P} {r R : ℝ}

/-- Inversion in a sphere in an affine space. This map sends each point `x` to the point `y` such
that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center and the radius the
sphere. -/
def inversion (c : P) (R : ℝ) (x : P) : P :=
  (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c
#align euclidean_geometry.inversion EuclideanGeometry.inversion

/-!
### Basic properties

In this section we prove that `EuclideanGeometry.inversion c R` is involutive and preserves the
sphere `Metric.sphere c R`. We also prove that the distance to the center of the image of `x` under
this inversion is given by `R ^ 2 / dist x c`.
-/

theorem inversion_eq_lineMap (c : P) (R : ℝ) (x : P) :
    inversion c R x = lineMap c x ((R / dist x c) ^ 2) :=
  rfl

theorem inversion_vsub_center (c : P) (R : ℝ) (x : P) :
    inversion c R x -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c) :=
  vadd_vsub _ _
#align euclidean_geometry.inversion_vsub_center EuclideanGeometry.inversion_vsub_center

@[simp]
theorem inversion_self (c : P) (R : ℝ) : inversion c R c = c := by simp [inversion]
                                                                   -- 🎉 no goals
#align euclidean_geometry.inversion_self EuclideanGeometry.inversion_self

@[simp]
theorem inversion_zero_radius (c x : P) : inversion c 0 x = c := by simp [inversion]
                                                                    -- 🎉 no goals

theorem inversion_mul (c : P) (a R : ℝ) (x : P) :
    inversion c (a * R) x = homothety c (a ^ 2) (inversion c R x) := by
  simp only [inversion_eq_lineMap, ← homothety_eq_lineMap, ← homothety_mul_apply, mul_div_assoc,
    mul_pow]

@[simp]
theorem inversion_dist_center (c x : P) : inversion c (dist x c) x = x := by
  rcases eq_or_ne x c with (rfl | hne)
  -- ⊢ inversion x (dist x x) x = x
  · apply inversion_self
    -- 🎉 no goals
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    -- ⊢ dist x c ≠ 0
    rwa [dist_ne_zero]
    -- 🎉 no goals
#align euclidean_geometry.inversion_dist_center EuclideanGeometry.inversion_dist_center

@[simp]
theorem inversion_dist_center' (c x : P) : inversion c (dist c x) x = x := by
  rw [dist_comm, inversion_dist_center]
  -- 🎉 no goals

theorem inversion_of_mem_sphere (h : x ∈ Metric.sphere c R) : inversion c R x = x :=
  h.out ▸ inversion_dist_center c x
#align euclidean_geometry.inversion_of_mem_sphere EuclideanGeometry.inversion_of_mem_sphere

/-- Distance from the image of a point under inversion to the center. This formula accidentally
works for `x = c`. -/
theorem dist_inversion_center (c x : P) (R : ℝ) : dist (inversion c R x) c = R ^ 2 / dist x c := by
  rcases eq_or_ne x c with (rfl | hx)
  -- ⊢ dist (inversion x R x) x = R ^ 2 / dist x x
  · simp
    -- 🎉 no goals
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  -- ⊢ dist (inversion c R x) c = R ^ 2 / dist x c
  field_simp [inversion, norm_smul, abs_div, ← dist_eq_norm_vsub, sq, mul_assoc]
  -- 🎉 no goals
#align euclidean_geometry.dist_inversion_center EuclideanGeometry.dist_inversion_center

/-- Distance from the center of an inversion to the image of a point under the inversion. This
formula accidentally works for `x = c`. -/
theorem dist_center_inversion (c x : P) (R : ℝ) : dist c (inversion c R x) = R ^ 2 / dist c x := by
  rw [dist_comm c, dist_comm c, dist_inversion_center]
  -- 🎉 no goals
#align euclidean_geometry.dist_center_inversion EuclideanGeometry.dist_center_inversion

@[simp]
theorem inversion_inversion (c : P) {R : ℝ} (hR : R ≠ 0) (x : P) :
    inversion c R (inversion c R x) = x := by
  rcases eq_or_ne x c with (rfl | hne)
  -- ⊢ inversion x R (inversion x R x) = x
  · rw [inversion_self, inversion_self]
    -- 🎉 no goals
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_pow,
      div_mul_div_comm, div_mul_cancel _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul,
      vsub_vadd]
    exact pow_ne_zero _ hR
    -- 🎉 no goals
#align euclidean_geometry.inversion_inversion EuclideanGeometry.inversion_inversion

theorem inversion_involutive (c : P) {R : ℝ} (hR : R ≠ 0) : Involutive (inversion c R) :=
  inversion_inversion c hR
#align euclidean_geometry.inversion_involutive EuclideanGeometry.inversion_involutive

theorem inversion_surjective (c : P) {R : ℝ} (hR : R ≠ 0) : Surjective (inversion c R) :=
  (inversion_involutive c hR).surjective
#align euclidean_geometry.inversion_surjective EuclideanGeometry.inversion_surjective

theorem inversion_injective (c : P) {R : ℝ} (hR : R ≠ 0) : Injective (inversion c R) :=
  (inversion_involutive c hR).injective
#align euclidean_geometry.inversion_injective EuclideanGeometry.inversion_injective

theorem inversion_bijective (c : P) {R : ℝ} (hR : R ≠ 0) : Bijective (inversion c R) :=
  (inversion_involutive c hR).bijective
#align euclidean_geometry.inversion_bijective EuclideanGeometry.inversion_bijective

theorem inversion_eq_center (hR : R ≠ 0) : inversion c R x = c ↔ x = c :=
  (inversion_injective c hR).eq_iff' <| inversion_self _ _

@[simp]
theorem inversion_eq_center' : inversion c R x = c ↔ x = c ∨ R = 0 := by
  by_cases hR : R = 0 <;> simp [inversion_eq_center, hR]
  -- ⊢ inversion c R x = c ↔ x = c ∨ R = 0
                          -- 🎉 no goals
                          -- 🎉 no goals

theorem center_eq_inversion (hR : R ≠ 0) : c = inversion c R x ↔ x = c :=
  eq_comm.trans (inversion_eq_center hR)

@[simp]
theorem center_eq_inversion' : c = inversion c R x ↔ x = c ∨ R = 0 :=
  eq_comm.trans inversion_eq_center'

/-!
### Similarity of triangles

If inversion with center `O` sends `A` to `A'` and `B` to `B'`, then the triangle `OB'A'` is similar
to the triangle `OAB` with coefficient `R ^ 2 / (|OA|*|OB|)` and the triangle `OA'B` is similar to
the triangle `OAB'` with coefficient `|OB|/|OA|`. We formulate these statements in terms of ratios
of the lengths of their sides.
-/

/-- Distance between the images of two points under an inversion. -/
theorem dist_inversion_inversion (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y := by
  dsimp only [inversion]
  -- ⊢ dist ((R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c) ((R / dist y c) ^ 2 • (y -ᵥ c) +ᵥ  …
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  -- ⊢ dist ((R / ‖x -ᵥ c‖) ^ 2 • (x -ᵥ c)) ((R / ‖y -ᵥ c‖) ^ 2 • (y -ᵥ c)) = R ^ 2 …
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R
#align euclidean_geometry.dist_inversion_inversion EuclideanGeometry.dist_inversion_inversion

theorem dist_inversion_mul_dist_center_eq (hx : x ≠ c) (hy : y ≠ c) :
    dist (inversion c R x) y * dist x c = dist x (inversion c R y) * dist y c := by
  rcases eq_or_ne R 0 with rfl | hR; · simp [dist_comm, mul_comm]
  -- ⊢ dist (inversion c 0 x) y * dist x c = dist x (inversion c 0 y) * dist y c
                                       -- 🎉 no goals
  have hy' : inversion c R y ≠ c := by simp [*]
  -- ⊢ dist (inversion c R x) y * dist x c = dist x (inversion c R y) * dist y c
  conv in dist _ y => rw [← inversion_inversion c hR y]
  -- ⊢ dist (inversion c R x) (inversion c R (inversion c R y)) * dist x c = dist x …
  rw [dist_inversion_inversion hx hy', dist_inversion_center]
  -- ⊢ R ^ 2 / (dist x c * (R ^ 2 / dist y c)) * dist x (inversion c R y) * dist x  …
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  -- ⊢ R ^ 2 / (dist x c * (R ^ 2 / dist y c)) * dist x (inversion c R y) * dist x  …
  field_simp; ring
  -- ⊢ R ^ 2 * dist y c * dist x (inversion c R y) * dist x c = dist x (inversion c …
              -- 🎉 no goals

/-!
### Ptolemy's inequality
-/

/-- **Ptolemy's inequality**: in a quadrangle `ABCD`, `|AC| * |BD| ≤ |AB| * |CD| + |BC| * |AD|`. If
`ABCD` is a convex cyclic polygon, then this inequality becomes an equality, see
`EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`. -/
theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  -- ⊢ dist b c * dist b d ≤ dist b b * dist c d + dist b c * dist b d
  · rw [dist_self, zero_mul, zero_add]
    -- 🎉 no goals
  rcases eq_or_ne c a with (rfl | hc)
  -- ⊢ dist c c * dist b d ≤ dist c b * dist c d + dist b c * dist c d
  · rw [dist_self, zero_mul]
    -- ⊢ 0 ≤ dist c b * dist c d + dist b c * dist c d
    apply_rules [add_nonneg, mul_nonneg, dist_nonneg]
    -- 🎉 no goals
  rcases eq_or_ne d a with (rfl | hd)
  -- ⊢ dist d c * dist b d ≤ dist d b * dist c d + dist b c * dist d d
  · rw [dist_self, mul_zero, add_zero, dist_comm d, dist_comm d, mul_comm]
    -- 🎉 no goals
  /- Otherwise, we apply the triangle inequality to `EuclideanGeometry.inversion a 1 b`,
    `EuclideanGeometry.inversion a 1 c`, and `EuclideanGeometry.inversion a 1 d`. -/
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)
  -- ⊢ dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d
  rw [dist_inversion_inversion hb hd, dist_inversion_inversion hb hc,
    dist_inversion_inversion hc hd, one_pow] at H
  rw [← dist_pos] at hb hc hd
  -- ⊢ dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d
  rw [← div_le_div_right (mul_pos hb (mul_pos hc hd))]
  -- ⊢ dist a c * dist b d / (dist b a * (dist c a * dist d a)) ≤ (dist a b * dist  …
  convert H using 1 <;> (field_simp [hb.ne', hc.ne', hd.ne', dist_comm a]; ring)
  -- ⊢ dist a c * dist b d / (dist b a * (dist c a * dist d a)) = 1 / (dist b a * d …
                         -- ⊢ dist c a * dist b d * (dist b a * dist d a) = dist b d * (dist b a * (dist c …
                                                                           -- 🎉 no goals
                         -- ⊢ (dist b a * dist c d + dist b c * dist d a) * (dist b a * dist c a * (dist c …
                                                                           -- 🎉 no goals
#align euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist

end EuclideanGeometry

open EuclideanGeometry

/-!
### Continuity of inversion
-/

protected theorem Filter.Tendsto.inversion {l : Filter α} {fc fx : α → P} {fR : α → ℝ}
    (hc : Tendsto fc l (𝓝 c)) (hR : Tendsto fR l (𝓝 R)) (hx : Tendsto fx l (𝓝 x))
    (hne : x ≠ c) :
    Tendsto (fun a ↦ inversion (fc a) (fR a) (fx a)) l (𝓝 (inversion c R x)) :=
  (((hR.div (hx.dist hc) <| dist_ne_zero.2 hne).pow 2).smul (hx.vsub hc)).vadd hc

variable {X : Type*} [TopologicalSpace X] {c x : X → P} {R : X → ℝ} {a₀ : X} {s : Set X}

protected nonrec theorem ContinuousWithinAt.inversion (hc : ContinuousWithinAt c s a₀)
    (hR : ContinuousWithinAt R s a₀) (hx : ContinuousWithinAt x s a₀) (hne : x a₀ ≠ c a₀) :
    ContinuousWithinAt (fun a ↦ inversion (c a) (R a) (x a)) s a₀ :=
  hc.inversion hR hx hne

protected nonrec theorem ContinuousAt.inversion (hc : ContinuousAt c a₀) (hR : ContinuousAt R a₀)
    (hx : ContinuousAt x a₀) (hne : x a₀ ≠ c a₀) :
    ContinuousAt (fun a ↦ inversion (c a) (R a) (x a)) a₀ :=
  hc.inversion hR hx hne

protected theorem ContinuousOn.inversion (hc : ContinuousOn c s) (hR : ContinuousOn R s)
    (hx : ContinuousOn x s) (hne : ∀ a ∈ s, x a ≠ c a) :
    ContinuousOn (fun a ↦ inversion (c a) (R a) (x a)) s := fun a ha ↦
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected theorem Continuous.inversion (hc : Continuous c) (hR : Continuous R) (hx : Continuous x)
    (hne : ∀ a, x a ≠ c a) : Continuous (fun a ↦ inversion (c a) (R a) (x a)) :=
  continuous_iff_continuousAt.2 fun _ ↦
    hc.continuousAt.inversion hR.continuousAt hx.continuousAt (hne _)
