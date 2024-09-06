/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Orientable Manifolds

This file defines orientable manifolds: a differentiable manifold is orientable if and only if it
admits an orientable atlas, i.e. an atlas whose transition functions have a strictly positive
Jacobian.

## Main Definitions

- `OrientationPreserving` : a map between normed spaces is orientation-preserving on a given set
  if the determinant of its Jacobian is strictly positive on that set.
- `OrientationReversing` : a map between normed spaces is orientation-reversing on a given set
  if the determinant of its Jacobian is strictly negative on that set.
- `orientationPreservingGroupoid` : the groupoid of partial homeos of `H` which are
  orientation-preserving.
- `OrientableManifold` : a type class saying that the charted space `M`, modelled on the space
  `H`, admits an orientation.
- `OrientableSmoothManifold` : a type class representing a manifold that is both orientable
  and smooth.

## Main Results

- `OrientationPreserving.differentiableAt` : an orientation preserving map is differentiable.
- `OrientationReversing.differentiableAt` : an orientation reversing map is differentiable.
- `orientationPreserving_comp` : a composition between two orientation preserving maps is
  orientation preserving.
- `orientationReversing_comp_orientationPreserving` : a composition between an orientation
  reversing map and an orientation preserving map is orientation reversing.
- `orientationPreserving_comp_orientationReversing` : a composition between an orientation
  preserving map and an orientation reversing map is orientation reversing.
- `orientationReversing_comp` : a composition between two orientation reversing maps is
  orientation preserving.

## TODO

- Generalize this discussion to any non-trivially normed field.
- On a given connected set, a diffeomorphism is either orientation preserving or orientation
  reversing.
- A normed space (with the trivial model) is orientable.
- The `n`-sphere is orientable.
- Products of orientable manifolds are orientable.
- Define orientations of a smooth manifold, and show that a manifold is orientable if and only if it
  admits an orientation.
- Define orientation preserving and reserving maps between manifolds.

## Implementation notes

The current definitions work for differentiable manifolds. For topological manifolds, orientability
can be defined using *local* orientations (which mathlib cannot state yet, as there is no e.g.
singular homology). In the future, it would be nice to generalise these definitions to allow for
topological manifolds also, and relate them to the current definition.

-/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section OrientationPreserving

/--
A map between normed spaces is orientation-preserving on a given set if it is differentiable and the
determinant of its Jacobian is strictly positive on that set.
-/
def OrientationPreserving (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, 0 < (fderiv ℝ f x).det

/--
A map between normed spaces is orientation-reversing on a given set if it is differentiable and the
determinant of its Jacobian is strictly negative on that set.
-/
def OrientationReversing (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, (fderiv ℝ f x).det < 0

lemma orientationPreserving_of_zero_dim (f : H → H) (s : Set H) (h : Module.rank ℝ H = 0) :
    OrientationPreserving f s :=
  fun _ _ ↦
  have det_eq_one : (fderiv ℝ f _).det = 1 := by
    have b : Basis (Fin 0) ℝ H := Basis.ofEquivFun (finDimVectorspaceEquiv 0 h)
    rw [ContinuousLinearMap.det, ← (fderiv ℝ f _).det_toMatrix b]
    exact Matrix.det_fin_zero
  det_eq_one ▸ Real.zero_lt_one

lemma OrientationPreserving.differentiableAt [FiniteDimensional ℝ H] {f : H → H} {s : Set H}
    (h : OrientationPreserving f s) {x : H} (hs : x ∈ s) : DifferentiableAt ℝ f x := by
  cases subsingleton_or_nontrivial H
  · apply DifferentiableWithinAt.differentiableAt
    apply Set.Subsingleton.differentiableOn
    exact s.subsingleton_of_subsingleton
    exact hs
    exact mem_nhds_discrete.mpr hs
  · unfold OrientationPreserving at h
    contrapose! h
    use x, hs
    rw [fderiv_zero_of_not_differentiableAt h, ContinuousLinearMap.det]
    simp [ne_of_gt FiniteDimensional.finrank_pos]

lemma OrientationReversing.differentiableAt {f : H → H} {s : Set H} (h : OrientationReversing f s)
    {x : H} (hs : x ∈ s) : DifferentiableAt ℝ f x := by
  unfold OrientationReversing at h
  contrapose! h
  use x, hs
  rw [fderiv_zero_of_not_differentiableAt h, ContinuousLinearMap.det]
  simp [ne_of_gt FiniteDimensional.finrank_pos]

lemma orientationPreserving_id (s : Set H) : OrientationPreserving id s := by
  intro
  simp [ContinuousLinearMap.det]

lemma orientationPreserving_comp [FiniteDimensional ℝ H] {f g : H → H} {u v : Set H}
    (hf : OrientationPreserving f u) (hg : OrientationPreserving g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_pos (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp_orientationPreserving [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationPreserving f u) (hg : OrientationReversing g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_neg_of_neg_of_pos (hg (f x) hxv) (hf x hxu)

lemma orientationPreserving_comp_orientationReversing [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationReversing f u) (hg : OrientationPreserving g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_neg_of_pos_of_neg (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp {f g : H → H} {u v : Set H}
    (hf : OrientationReversing f u) (hg : OrientationReversing g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_pos_of_neg_of_neg (hg (f x) hxv) (hf x hxu)

/-- The pregroupoid of orientation-preserving maps. -/
def orientationPreservingPregroupoid [FiniteDimensional ℝ H] : Pregroupoid H where
  property f s := OrientationPreserving f s
  comp hf hg _ _ _ _ hx := orientationPreserving_comp hf hg _ hx
  id_mem := orientationPreserving_id _
  locality {f u} _ h x hxu :=
    have ⟨v, _, hxv, h⟩ := h x hxu
    h x <| Set.mem_inter hxu hxv
  congr {f g u} hu fg hf x hx := by
    rw [(Filter.eventuallyEq_of_mem (hu.mem_nhds hx) fg).fderiv_eq]
    exact hf x hx

/-- The groupoid of orientation-preserving maps. -/
def orientationPreservingGroupoid [FiniteDimensional ℝ H] : StructureGroupoid H :=
  orientationPreservingPregroupoid.groupoid

end OrientationPreserving

section OrientableManifold

/-! ### Orientable manifolds -/


/-- Typeclass defining orientable manifolds. -/
class OrientableManifold (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M] extends
  HasGroupoid M (@orientationPreservingGroupoid H _ _ _) : Prop

/-- `0`-dimensional manifolds are always orientable. -/
lemma orientableManifold_of_zero_dim (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (h : Module.rank ℝ H = 0) : OrientableManifold H M where
  compatible := fun {_ _} _ _ ↦
    ⟨orientationPreserving_of_zero_dim _ _ h, orientationPreserving_of_zero_dim _ _ h⟩

/-- Typeclass defining orientable smooth manifolds. -/
class OrientableSmoothManifold (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ E H) extends
  HasGroupoid M ((contDiffGroupoid ⊤ I) ⊓ orientationPreservingGroupoid) : Prop

end OrientableManifold
