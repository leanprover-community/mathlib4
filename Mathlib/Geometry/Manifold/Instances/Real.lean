/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module geometry.manifold.instances.real
! leanprover-community/mathlib commit 6a033cb3d188a12ca5c509b33e2eaac1c61916cd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`.

More specifically, we introduce
* `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary
* `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notations

In the locale `manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `euclidean_space ℝ (fin n)`
* `𝓡∂ n` for `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n)`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `euclidean_space ℝ (fin m)`,
and `N` is smooth with boundary modelled on `euclidean_half_space n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners can not be implicit, see the discussion in `smooth_manifold_with_corners.lean`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[fact (x < y)]`.
-/


noncomputable section

open Set Function

open scoped Manifold

/-- The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
def EuclideanHalfSpace (n : ℕ) [Zero (Fin n)] : Type :=
  { x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0 }
#align euclidean_half_space EuclideanHalfSpace

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
def EuclideanQuadrant (n : ℕ) : Type :=
  { x : EuclideanSpace ℝ (Fin n) // ∀ i : Fin n, 0 ≤ x i }
#align euclidean_quadrant EuclideanQuadrant

section

/- Register class instances for euclidean half-space and quadrant, that can not be noticed
without the following reducibility attribute (which is only set in this section). -/
attribute [local reducible] EuclideanHalfSpace EuclideanQuadrant

variable {n : ℕ}

instance [Zero (Fin n)] : TopologicalSpace (EuclideanHalfSpace n) := by infer_instance

instance : TopologicalSpace (EuclideanQuadrant n) := by infer_instance

instance [Zero (Fin n)] : Inhabited (EuclideanHalfSpace n) :=
  ⟨⟨0, le_rfl⟩⟩

instance : Inhabited (EuclideanQuadrant n) :=
  ⟨⟨0, fun i => le_rfl⟩⟩

theorem range_half_space (n : ℕ) [Zero (Fin n)] :
    (range fun x : EuclideanHalfSpace n => x.val) = { y | 0 ≤ y 0 } := by simp
#align range_half_space range_half_space

theorem range_quadrant (n : ℕ) :
    (range fun x : EuclideanQuadrant n => x.val) = { y | ∀ i : Fin n, 0 ≤ y i } := by simp
#align range_quadrant range_quadrant

end

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∈ » ({0} : set[set] (fin[fin] n))) -/
/--
Definition of the model with corners `(euclidean_space ℝ (fin n), euclidean_half_space n)`, used as
a model for manifolds with boundary. In the locale `manifold`, use the shortcut `𝓡∂ n`.
-/
def modelWithCornersEuclideanHalfSpace (n : ℕ) [Zero (Fin n)] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)
    where
  toFun := Subtype.val
  invFun x := ⟨update x 0 (max (x 0) 0), by simp [le_refl]⟩
  source := univ
  target := { x | 0 ≤ x 0 }
  map_source' x hx := x.property
  map_target' x hx := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ hx =>
    by
    rw [Subtype.mk_eq_mk, update_eq_iff]
    exact ⟨max_eq_left xprop, fun i _ => rfl⟩
  right_inv' x hx := update_eq_iff.2 ⟨max_eq_left hx, fun i _ => rfl⟩
  source_eq := rfl
  unique_diff' :=
    by
    have this : UniqueDiffOn ℝ _ :=
      UniqueDiffOn.pi (Fin n) (fun _ => ℝ) _ _ fun i (_ : i ∈ ({0} : Set (Fin n))) =>
        uniqueDiffOn_Ici 0
    simpa only [singleton_pi] using this
  continuous_toFun := continuous_subtype_val
  continuous_invFun :=
    (continuous_id.update 0 <| (continuous_apply 0).max continuous_const).subtype_mk _
#align model_with_corners_euclidean_half_space modelWithCornersEuclideanHalfSpace

/--
Definition of the model with corners `(euclidean_space ℝ (fin n), euclidean_quadrant n)`, used as a
model for manifolds with corners -/
def modelWithCornersEuclideanQuadrant (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)
    where
  toFun := Subtype.val
  invFun x := ⟨fun i => max (x i) 0, fun i => by simp only [le_refl, or_true_iff, le_max_iff]⟩
  source := univ
  target := { x | ∀ i, 0 ≤ x i }
  map_source' x hx := by simpa only [Subtype.range_val] using x.property
  map_target' x hx := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ hx => by ext i; simp only [Subtype.coe_mk, xprop i, max_eq_left]
  right_inv' x hx := by ext1 i; simp only [hx i, max_eq_left]
  source_eq := rfl
  unique_diff' :=
    by
    have this : UniqueDiffOn ℝ _ :=
      UniqueDiffOn.univ_pi (Fin n) (fun _ => ℝ) _ fun i => uniqueDiffOn_Ici 0
    simpa only [pi_univ_Ici] using this
  continuous_toFun := continuous_subtype_val
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => (continuous_id.max continuous_const).comp (continuous_apply i)) _
#align model_with_corners_euclidean_quadrant modelWithCornersEuclideanQuadrant

-- mathport name: model_with_corners_self.euclidean
scoped[Manifold]
  notation "𝓡 " n =>
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))

-- mathport name: model_with_corners_euclidean_half_space.euclidean
scoped[Manifold]
  notation "𝓡∂ " n =>
    (modelWithCornersEuclideanHalfSpace n :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n))

/-- The left chart for the topological space `[x, y]`, defined on `[x,y)` and sending `x` to `0` in
`euclidean_half_space 1`.
-/
def iccLeftChart (x y : ℝ) [Fact (x < y)] : LocalHomeomorph (Icc x y) (EuclideanHalfSpace 1)
    where
  source := { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨fun i => z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [le_refl, z.prop, le_of_lt (Fact.out (x < y))]⟩
  map_source' := by simp only [imp_self, sub_lt_sub_iff_right, mem_set_of_eq, forall_true_iff]
  map_target' := by
    simp only [min_lt_iff, mem_set_of_eq]; intro z hz; left
    dsimp [-Subtype.val_eq_coe] at hz ; linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_set_of_eq, mem_Icc] at hz h'z 
    simp only [hz, min_eq_left, sub_add_cancel]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    funext
    dsimp at hz h'z 
    have A : x + z 0 ≤ y := by linarith
    rw [Subsingleton.elim i 0]
    simp only [A, add_comm, add_sub_cancel', min_eq_left]
  open_source :=
    haveI : IsOpen { z : ℝ | z < y } := isOpen_Iio
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@continuous_apply (Fin 1) (fun _ => ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuous_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have : Continuous fun (z : ℝ) (i : Fin 1) => z - x :=
      Continuous.sub (continuous_pi fun i => continuous_id) continuous_const
    exact this.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have A : Continuous fun z : ℝ => min (z + x) y :=
      (continuous_id.add continuous_const).min continuous_const
    have B : Continuous fun z : EuclideanSpace ℝ (Fin 1) => z 0 := continuous_apply 0
    exact (A.comp B).comp continuous_subtype_val
#align Icc_left_chart iccLeftChart

/-- The right chart for the topological space `[x, y]`, defined on `(x,y]` and sending `y` to `0` in
`euclidean_half_space 1`.
-/
def iccRightChart (x y : ℝ) [Fact (x < y)] : LocalHomeomorph (Icc x y) (EuclideanHalfSpace 1)
    where
  source := { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨fun i => y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [le_refl, z.prop, le_of_lt (Fact.out (x < y)), sub_eq_add_neg]⟩
  map_source' := by simp only [imp_self, mem_set_of_eq, sub_lt_sub_iff_left, forall_true_iff]
  map_target' := by
    simp only [lt_max_iff, mem_set_of_eq]; intro z hz; left
    dsimp [-Subtype.val_eq_coe] at hz ; linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_set_of_eq, mem_Icc] at hz h'z 
    simp only [hz, sub_eq_add_neg, max_eq_left, add_add_neg_cancel'_right, neg_add_rev, neg_neg]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    funext
    dsimp at hz h'z 
    have A : x ≤ y - z 0 := by linarith
    rw [Subsingleton.elim i 0]
    simp only [A, sub_sub_cancel, max_eq_left]
  open_source :=
    haveI : IsOpen { z : ℝ | x < z } := isOpen_Ioi
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@continuous_apply (Fin 1) (fun _ => ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuous_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have : Continuous fun (z : ℝ) (i : Fin 1) => y - z :=
      continuous_const.sub (continuous_pi fun i => continuous_id)
    exact this.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have A : Continuous fun z : ℝ => max (y - z) x :=
      (continuous_const.sub continuous_id).max continuous_const
    have B : Continuous fun z : EuclideanSpace ℝ (Fin 1) => z 0 := continuous_apply 0
    exact (A.comp B).comp continuous_subtype_val
#align Icc_right_chart iccRightChart

/-- Charted space structure on `[x, y]`, using only two charts taking values in
`euclidean_half_space 1`.
-/
instance iccManifold (x y : ℝ) [Fact (x < y)] : ChartedSpace (EuclideanHalfSpace 1) (Icc x y)
    where
  atlas := {iccLeftChart x y, iccRightChart x y}
  chartAt z := if z.val < y then iccLeftChart x y else iccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le (Fact.out (x < y))
      simpa only [not_lt] using h'
  chart_mem_atlas z := by by_cases h' : (z : ℝ) < y <;> simp [h']
#align Icc_manifold iccManifold

/-- The manifold structure on `[x, y]` is smooth.
-/
instance Icc_smooth_manifold (x y : ℝ) [Fact (x < y)] :
    SmoothManifoldWithCorners (𝓡∂ 1) (Icc x y) :=
  by
  have M : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 1) => -z + fun i => y - x) univ :=
    by
    rw [contDiffOn_univ]
    exact cont_diff_id.neg.add contDiff_const
  apply smoothManifoldWithCorners_of_contDiffOn
  intro e e' he he'
  simp only [atlas, mem_singleton_iff, mem_insert_iff] at he he' 
  /- We need to check that any composition of two charts gives a `C^∞` function. Each chart can be
      either the left chart or the right chart, leaving 4 possibilities that we handle successively.
      -/
    rcases he with (rfl | rfl) <;>
    rcases he' with (rfl | rfl)
  ·-- `e = left chart`, `e' = left chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _ _ _)).1
  · -- `e = left chart`, `e' = right chart`
    apply M.congr_mono _ (subset_univ _)
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [modelWithCornersEuclideanHalfSpace, iccLeftChart, iccRightChart, update_same,
      max_eq_left, hz₀, lt_sub_iff_add_lt, mfld_simps] at hz₁ hz₂ 
    rw [min_eq_left hz₁.le, lt_add_iff_pos_left] at hz₂ 
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, iccLeftChart, iccRightChart, *, PiLp.add_apply,
      PiLp.neg_apply, max_eq_left, min_eq_left hz₁.le, update_same, mfld_simps]
    abel
  · -- `e = right chart`, `e' = left chart`
    apply M.congr_mono _ (subset_univ _)
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨z, hz₀⟩, rfl⟩
    simp only [modelWithCornersEuclideanHalfSpace, iccLeftChart, iccRightChart, max_lt_iff,
      update_same, max_eq_left hz₀, mfld_simps] at hz₁ hz₂ 
    rw [lt_sub_comm] at hz₁ 
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, iccLeftChart, iccRightChart, PiLp.add_apply,
      PiLp.neg_apply, update_same, max_eq_left, hz₀, hz₁.le, mfld_simps]
    abel
  ·-- `e = right chart`, `e' = right chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _ _ _)).1
#align Icc_smooth_manifold Icc_smooth_manifold

/-! Register the manifold structure on `Icc 0 1`, and also its zero and one. -/


section

attribute [local instance] Real.fact_zero_lt_one

instance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1) := by infer_instance

instance : SmoothManifoldWithCorners (𝓡∂ 1) (Icc (0 : ℝ) 1) := by infer_instance

end

