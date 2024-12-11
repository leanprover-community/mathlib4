/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`, and prove that its boundary is indeed `{x,y}`
whenever `x < y`.

More specifically, we introduce
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary
* `modelWithCornersEuclideanQuadrant n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notations

In the locale `Manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `EuclideanSpace ℝ (Fin n)`
* `𝓡∂ n` for `modelWithCornersEuclideanHalfSpace n`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `EuclideanSpace ℝ (Fin m)`,
and `N` is smooth with boundary modelled on `EuclideanHalfSpace n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners can not be implicit, see the discussion in
`Geometry.Manifold.SmoothManifoldWithCorners`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[Fact (x < y)]`.
-/


noncomputable section

open Set Function

open scoped Manifold ContDiff

/-- The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
def EuclideanHalfSpace (n : ℕ) [NeZero n] : Type :=
  { x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0 }

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
def EuclideanQuadrant (n : ℕ) : Type :=
  { x : EuclideanSpace ℝ (Fin n) // ∀ i : Fin n, 0 ≤ x i }

section

/- Register class instances for euclidean half-space and quadrant, that can not be noticed
without the following reducibility attribute (which is only set in this section). -/

variable {n : ℕ}

instance [NeZero n] : TopologicalSpace (EuclideanHalfSpace n) :=
  instTopologicalSpaceSubtype

instance : TopologicalSpace (EuclideanQuadrant n) :=
  instTopologicalSpaceSubtype

instance [NeZero n] : Inhabited (EuclideanHalfSpace n) :=
  ⟨⟨0, le_rfl⟩⟩

instance : Inhabited (EuclideanQuadrant n) :=
  ⟨⟨0, fun _ => le_rfl⟩⟩

@[ext]
theorem EuclideanQuadrant.ext (x y : EuclideanQuadrant n) (h : x.1 = y.1) : x = y :=
  Subtype.eq h

@[ext]
theorem EuclideanHalfSpace.ext [NeZero n] (x y : EuclideanHalfSpace n)
    (h : x.1 = y.1) : x = y :=
  Subtype.eq h

theorem EuclideanHalfSpace.convex [NeZero n] :
    Convex ℝ { x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 } :=
  fun _ hx _ hy _ _ _ _ _ ↦ by dsimp at hx hy ⊢; positivity

theorem EuclideanQuadrant.convex :
    Convex ℝ { x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i } :=
  fun _ hx _ hy _ _ _ _ _ i ↦ by dsimp at hx hy ⊢; specialize hx i; specialize hy i; positivity

instance EuclideanHalfSpace.pathConnectedSpace [NeZero n] :
    PathConnectedSpace (EuclideanHalfSpace n) :=
  isPathConnected_iff_pathConnectedSpace.mp <| convex.isPathConnected ⟨0, by simp⟩

instance EuclideanQuadrant.pathConnectedSpace : PathConnectedSpace (EuclideanQuadrant n) :=
  isPathConnected_iff_pathConnectedSpace.mp <| convex.isPathConnected ⟨0, by simp⟩

instance [NeZero n] : LocPathConnectedSpace (EuclideanHalfSpace n) :=
  EuclideanHalfSpace.convex.locPathConnectedSpace

instance : LocPathConnectedSpace (EuclideanQuadrant n) :=
  EuclideanQuadrant.convex.locPathConnectedSpace

theorem range_euclideanHalfSpace (n : ℕ) [NeZero n] :
    (range fun x : EuclideanHalfSpace n => x.val) = { y | 0 ≤ y 0 } :=
  Subtype.range_val
@[deprecated (since := "2024-04-05")] alias range_half_space := range_euclideanHalfSpace

open ENNReal in
@[simp]
theorem interior_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    interior { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a < y i } := by
  let f : (Π _ : Fin n, ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change interior (f ⁻¹' Ici a) = f ⁻¹' Ioi a
  rw [f.interior_preimage, interior_Ici]
  apply Function.surjective_eval

@[deprecated (since := "2024-11-12")] alias interior_halfspace := interior_halfSpace

open ENNReal in
@[simp]
theorem closure_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a ≤ y i } := by
  let f : (Π _ : Fin n, ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change closure (f ⁻¹' Ici a) = f ⁻¹' Ici a
  rw [f.closure_preimage, closure_Ici]
  apply Function.surjective_eval

@[deprecated (since := "2024-11-12")] alias closure_halfspace := closure_halfSpace

open ENNReal in
@[simp]
theorem closure_open_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | a < y i } = { y | a ≤ y i } := by
  let f : (Π _ : Fin n, ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change closure (f ⁻¹' Ioi a) = f ⁻¹' Ici a
  rw [f.closure_preimage, closure_Ioi]
  apply Function.surjective_eval

@[deprecated (since := "2024-11-12")] alias closure_open_halfspace := closure_open_halfSpace

open ENNReal in
@[simp]
theorem frontier_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    frontier { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a = y i } := by
  rw [frontier, closure_halfSpace, interior_halfSpace]
  ext y
  simpa only [mem_diff, mem_setOf_eq, not_lt] using antisymm_iff
@[deprecated (since := "2024-11-12")] alias frontier_halfspace := frontier_halfSpace

theorem range_euclideanQuadrant (n : ℕ) :
    (range fun x : EuclideanQuadrant n => x.val) = { y | ∀ i : Fin n, 0 ≤ y i } :=
  Subtype.range_val
@[deprecated (since := "2024-04-05")] alias range_quadrant := range_euclideanQuadrant

end

/--
Definition of the model with corners `(EuclideanSpace ℝ (Fin n), EuclideanHalfSpace n)`, used as
a model for manifolds with boundary. In the locale `Manifold`, use the shortcut `𝓡∂ n`.
-/
def modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) where
  toFun := Subtype.val
  invFun x := ⟨update x 0 (max (x 0) 0), by simp [le_refl]⟩
  source := univ
  target := { x | 0 ≤ x 0 }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ _ => by
    rw [Subtype.mk_eq_mk, update_eq_iff]
    exact ⟨max_eq_left xprop, fun i _ => rfl⟩
  right_inv' _ hx := update_eq_iff.2 ⟨max_eq_left hx, fun _ _ => rfl⟩
  source_eq := rfl
  uniqueDiffOn' := by
    have : UniqueDiffOn ℝ _ :=
      UniqueDiffOn.pi (Fin n) (fun _ => ℝ) _ _ fun i (_ : i ∈ ({0} : Set (Fin n))) =>
        uniqueDiffOn_Ici 0
    simpa only [singleton_pi] using this
  target_subset_closure_interior := by simp
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by
    exact (continuous_id.update 0 <| (continuous_apply 0).max continuous_const).subtype_mk _

/--
Definition of the model with corners `(EuclideanSpace ℝ (Fin n), EuclideanQuadrant n)`, used as a
model for manifolds with corners -/
def modelWithCornersEuclideanQuadrant (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n) where
  toFun := Subtype.val
  invFun x := ⟨fun i => max (x i) 0, fun i => by simp only [le_refl, or_true, le_max_iff]⟩
  source := univ
  target := { x | ∀ i, 0 ≤ x i }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := by ext i; simp only [Subtype.coe_mk, x.2 i, max_eq_left]
  right_inv' x hx := by ext1 i; simp only [hx i, max_eq_left]
  source_eq := rfl
  uniqueDiffOn' := by
    have this : UniqueDiffOn ℝ _ :=
      UniqueDiffOn.univ_pi (Fin n) (fun _ => ℝ) _ fun _ => uniqueDiffOn_Ici 0
    simpa only [pi_univ_Ici] using this
  target_subset_closure_interior := by
    have : {x : EuclideanSpace ℝ (Fin n) | ∀ (i : Fin n), 0 ≤ x i}
      = Set.pi univ (fun i ↦ Ici 0) := by aesop
    simp only [this, interior_pi_set finite_univ]
    rw [closure_pi_set]
    simp
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk
    (continuous_pi fun i => (continuous_id.max continuous_const).comp (continuous_apply i)) _

/-- The model space used to define `n`-dimensional real manifolds without boundary. -/
scoped[Manifold]
  notation3 "𝓡 " n =>
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))

/-- The model space used to define `n`-dimensional real manifolds with boundary. -/
scoped[Manifold]
  notation3 "𝓡∂ " n =>
    (modelWithCornersEuclideanHalfSpace n :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n))

lemma range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    range (𝓡∂ n) = { y | 0 ≤ y 0 } := range_euclideanHalfSpace n

lemma interior_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    interior (range (𝓡∂ n)) = { y | 0 < y 0 } := by
  calc interior (range (𝓡∂ n))
    _ = interior ({ y | 0 ≤ y 0}) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 < y 0 } := interior_halfSpace _ _ _

lemma frontier_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    frontier (range (𝓡∂ n)) = { y | 0 = y 0 } := by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 ≤ y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfSpace 2 _ _

/-- The left chart for the topological space `[x, y]`, defined on `[x,y)` and sending `x` to `0` in
`EuclideanHalfSpace 1`.
-/
def IccLeftChart (x y : ℝ) [h : Fact (x < y)] :
    PartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨fun _ => z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [le_refl, z.prop, le_of_lt h.out]⟩
  map_source' := by simp only [imp_self, sub_lt_sub_iff_right, mem_setOf_eq, forall_true_iff]
  map_target' := by
    simp only [min_lt_iff, mem_setOf_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_setOf_eq, mem_Icc] at hz h'z
    simp only [hz, min_eq_left, sub_add_cancel]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    funext i
    dsimp at hz h'z
    have A : x + z 0 ≤ y := by linarith
    rw [Subsingleton.elim i 0]
    simp only [A, add_comm, add_sub_cancel_left, min_eq_left]
  open_source :=
    haveI : IsOpen { z : ℝ | z < y } := isOpen_Iio
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@continuous_apply (Fin 1) (fun _ => ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have : Continuous fun (z : ℝ) (_ : Fin 1) => z - x :=
      Continuous.sub (continuous_pi fun _ => continuous_id) continuous_const
    exact this.comp continuous_subtype_val
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have A : Continuous fun z : ℝ => min (z + x) y :=
      (continuous_id.add continuous_const).min continuous_const
    have B : Continuous fun z : EuclideanSpace ℝ (Fin 1) => z 0 := continuous_apply 0
    exact (A.comp B).comp continuous_subtype_val

variable {x y : ℝ} [hxy : Fact (x < y)]

/-- The endpoint `x ∈ Icc x y`, as a point in `Icc x y` (assuming `x ≤ y`). -/
abbrev X : Icc x y := ⟨x, ⟨le_refl x, by have := hxy.out; linarith⟩⟩

/-- The endpoint `y ∈ Icc x y`, as a point in `Icc x y` (assuming `x ≤ y`). -/
abbrev Y : Icc x y := ⟨y, ⟨by have := hxy.out; linarith, le_refl y⟩⟩

lemma IccLeftChart_extend_left_eq : ((IccLeftChart x y).extend (𝓡∂ 1)) X = 0 := by
  let zero : EuclideanHalfSpace 1 := ⟨fun _ ↦ 0, by norm_num⟩
  calc ((IccLeftChart x y).extend (𝓡∂ 1)) X
    _ = (𝓡∂ 1) ((IccLeftChart x y) X) := rfl
    _ = (𝓡∂ 1) zero := by
      congr; ext; rw [IccLeftChart]
      norm_num
    _ = 0 := rfl

lemma IccLeftChart_extend_interior_pos {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    (((IccLeftChart x y).extend (𝓡∂ 1)) p) 0 > 0 := by
  set lhs := (IccLeftChart x y).extend (𝓡∂ 1) p
  have : lhs 0 = p.val - x := rfl
  rw [this]
  norm_num [hp.1]

lemma IccLeftChart_boundary : (IccLeftChart x y).extend (𝓡∂ 1) X ∈ frontier (range (𝓡∂ 1)) := by
  rw [IccLeftChart_extend_left_eq, frontier_range_modelWithCornersEuclideanHalfSpace]
  exact rfl

/-- The right chart for the topological space `[x, y]`, defined on `(x,y]` and sending `y` to `0` in
`EuclideanHalfSpace 1`.
-/
def IccRightChart (x y : ℝ) [h : Fact (x < y)] :
    PartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun z := ⟨fun _ => y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [le_refl, z.prop, le_of_lt h.out, sub_eq_add_neg]⟩
  map_source' := by simp only [imp_self, mem_setOf_eq, sub_lt_sub_iff_left, forall_true_iff]
  map_target' := by
    simp only [lt_max_iff, mem_setOf_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_setOf_eq, mem_Icc] at hz h'z
    simp only [hz, sub_eq_add_neg, max_eq_left, add_add_neg_cancel'_right, neg_add_rev, neg_neg]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    funext i
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
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have : Continuous fun (z : ℝ) (_ : Fin 1) => y - z :=
      continuous_const.sub (continuous_pi fun _ => continuous_id)
    exact this.comp continuous_subtype_val
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have A : Continuous fun z : ℝ => max (y - z) x :=
      (continuous_const.sub continuous_id).max continuous_const
    have B : Continuous fun z : EuclideanSpace ℝ (Fin 1) => z 0 := continuous_apply 0
    exact (A.comp B).comp continuous_subtype_val

lemma IccRightChart_extend_right_eq : (IccRightChart x y).extend (𝓡∂ 1) Y = 0 := by
  let zero : EuclideanHalfSpace 1 := ⟨fun _ ↦ 0, by norm_num⟩
  calc ((IccRightChart x y).extend (𝓡∂ 1)) Y
    _ = (𝓡∂ 1) ((IccRightChart x y) Y) := rfl
    _ = (𝓡∂ 1) zero := by
      congr; ext; rw [IccRightChart]
      norm_num
    _ = 0 := rfl

lemma IccRightChart_boundary : (IccRightChart x y).extend (𝓡∂ 1) Y ∈ frontier (range (𝓡∂ 1)) := by
  rw [IccRightChart_extend_right_eq, frontier_range_modelWithCornersEuclideanHalfSpace]
  exact rfl

/-- Charted space structure on `[x, y]`, using only two charts taking values in
`EuclideanHalfSpace 1`.
-/
instance IccChartedSpace (x y : ℝ) [h : Fact (x < y)] :
    ChartedSpace (EuclideanHalfSpace 1) (Icc x y) where
  atlas := {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt] using h'
  chart_mem_atlas z := by by_cases h' : (z : ℝ) < y <;> simp [h']

/-- Copy of `IccManifold`, to be able to state a lemma about its charts at a specific point. -/
def IccManifold2 (x y : ℝ) [h : Fact (x < y)] :
    ChartedSpace (EuclideanHalfSpace 1) (Icc x y) where
  atlas := {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt] using h'
  chart_mem_atlas z := by by_cases h' : (z : ℝ) < y <;> simp [h']

lemma IccManifold2.leftCharts {x y : ℝ} [h : Fact (x < y)] {z : Set.Icc x y} (h : z.val < y) :
    (IccManifold2 x y).chartAt z = IccLeftChart x y := by
  unfold IccManifold2
  simp_all only [reduceIte]

lemma IccManifold2.rightCharts {x y : ℝ} [h : Fact (x < y)] {z : Set.Icc x y} (h : z.val ≥ y) :
    (IccManifold2 x y).chartAt z = IccRightChart x y := by
  unfold IccManifold2
  simp_all only [reduceIte, not_lt.mpr h]

lemma Icc_isBoundaryPoint_left : (𝓡∂ 1).IsBoundaryPoint (X : Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt]
  have : chartAt (EuclideanHalfSpace 1) X = IccLeftChart x y :=
    IccManifold2.leftCharts (by norm_num [hxy.out])
  suffices ((IccLeftChart x y).extend (𝓡∂ 1)) X ∈ frontier (range (𝓡∂ 1)) by convert this
  exact IccLeftChart_boundary

lemma Icc_isBoundaryPoint_right : (𝓡∂ 1).IsBoundaryPoint (Y : Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt]
  have : chartAt (EuclideanHalfSpace 1) Y = IccRightChart x y := by
    apply IccManifold2.rightCharts (by norm_num)
  suffices ((IccRightChart x y).extend (𝓡∂ 1)) Y ∈ frontier (range (𝓡∂ 1)) by convert this
  exact IccRightChart_boundary

lemma Icc_isInteriorPoint_interior {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    (𝓡∂ 1).IsInteriorPoint p := by
  have : chartAt (EuclideanHalfSpace 1) p = IccLeftChart x y := IccManifold2.leftCharts hp.2
  suffices ((IccLeftChart x y).extend (𝓡∂ 1)) p ∈ interior (range (𝓡∂ 1)) by
    rw [ModelWithCorners.IsInteriorPoint, extChartAt]
    convert this
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  apply IccLeftChart_extend_interior_pos hp

lemma boundary_IccManifold : (𝓡∂ 1).boundary (Icc x y) = { X, Y } := by
  ext p
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p.2 with (hp | hp | hp)
  · have : p = X := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_left (mem_insert X {Y})
  · have : p = Y := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_right (mem_insert_of_mem X rfl)
  · apply iff_of_false
    · -- FIXME: golf using compl_boundary once #14972 has landed
      rw [ModelWithCorners.boundary_eq_complement_interior, not_mem_compl_iff]
      exact Icc_isInteriorPoint_interior hp
    · rw [mem_insert_iff, mem_singleton_iff]
      push_neg
      constructor <;> by_contra h <;> rw [congrArg Subtype.val h] at hp
      · apply left_mem_Ioo.mp hp
      · apply right_mem_Ioo.mp hp

/-- The manifold structure on `[x, y]` is smooth.
-/
instance Icc_smoothManifoldWithCorners (x y : ℝ) [Fact (x < y)] :
    SmoothManifoldWithCorners (𝓡∂ 1) (Icc x y) := by
  have M : ContDiff ℝ ∞ (show EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      from fun z i => -z i + (y - x)) :=
    contDiff_id.neg.add contDiff_const
  apply smoothManifoldWithCorners_of_contDiffOn
  intro e e' he he'
  simp only [atlas, mem_singleton_iff, mem_insert_iff] at he he'
  /- We need to check that any composition of two charts gives a `C^∞` function. Each chart can be
  either the left chart or the right chart, leaving 4 possibilities that we handle successively. -/
  rcases he with (rfl | rfl) <;> rcases he' with (rfl | rfl)
  · -- `e = left chart`, `e' = left chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
  · -- `e = left chart`, `e' = right chart`
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, update_same,
      max_eq_left, hz₀, lt_sub_iff_add_lt, mfld_simps] at hz₁ hz₂
    rw [min_eq_left hz₁.le, lt_add_iff_pos_left] at hz₂
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, *, PiLp.add_apply,
      PiLp.neg_apply, max_eq_left, min_eq_left hz₁.le, update_same, mfld_simps]
    abel
  · -- `e = right chart`, `e' = left chart`
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨z, hz₀⟩, rfl⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, max_lt_iff,
      update_same, max_eq_left hz₀, mfld_simps] at hz₁ hz₂
    rw [lt_sub_comm] at hz₁
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, PiLp.add_apply,
      PiLp.neg_apply, update_same, max_eq_left, hz₀, hz₁.le, mfld_simps]
    abel
  ·-- `e = right chart`, `e' = right chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1

/-! Register the manifold structure on `Icc 0 1`. These are merely special cases of
`IccChartedSpace` and `Icc_smoothManifoldWithCorners`. -/

section

instance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1) := by infer_instance

instance : SmoothManifoldWithCorners (𝓡∂ 1) (Icc (0 : ℝ) 1) := by infer_instance

end
