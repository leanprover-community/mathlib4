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
- `OrientableManifold`: a type class saying that the charted space `M`, modelled on the space `H`,
  admits an orientation.

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

lemma orientationPreserving_of_zero_dim (f : H → H) (s : Set H)
    (h : FiniteDimensional.finrank ℝ H = 0) : OrientationPreserving f s := by
  intro _ _
  simp [LinearMap.det_eq_one_of_finrank_eq_zero h]

lemma OrientationPreserving.differentiableAt [FiniteDimensional ℝ H] {f : H → H} {s : Set H}
    (h : OrientationPreserving f s) {x : H} (hs : x ∈ s) : DifferentiableAt ℝ f x := by
  cases subsingleton_or_nontrivial H
  · apply ((s.subsingleton_of_subsingleton).differentiableOn _ hs).differentiableAt
    exact mem_nhds_discrete.mpr hs
  · rw [OrientationPreserving] at h
    contrapose! h
    use x, hs
    rw [fderiv_zero_of_not_differentiableAt h, ContinuousLinearMap.det]
    simp [ne_of_gt FiniteDimensional.finrank_pos]

lemma OrientationReversing.differentiableAt {f : H → H} {s : Set H} (h : OrientationReversing f s)
    {x : H} (hs : x ∈ s) : DifferentiableAt ℝ f x := by
  rw [OrientationReversing] at h
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
  simpa [ContinuousLinearMap.det] using mul_pos (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp_orientationPreserving [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationPreserving f u) (hg : OrientationReversing g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa [ContinuousLinearMap.det] using mul_neg_of_neg_of_pos (hg (f x) hxv) (hf x hxu)

lemma orientationPreserving_comp_orientationReversing [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationReversing f u) (hg : OrientationPreserving g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa [ContinuousLinearMap.det] using mul_neg_of_pos_of_neg (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp {f g : H → H} {u v : Set H}
    (hf : OrientationReversing f u) (hg : OrientationReversing g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa [ContinuousLinearMap.det] using mul_pos_of_neg_of_neg (hg (f x) hxv) (hf x hxu)

/-- A linear isomorphism on a connected set is
either orientation-preserving or orientation-reversing. -/
lemma foo (f : H ≃L[ℝ] H) {s : Set H} (hs : IsConnected s) (hs' : IsPathConnected s) :
    OrientationPreserving f s ∨ OrientationReversing f s := by
  -- At each point, its determinant is non-zero, as it is a diffeomorphism.
  have (x : H) : (fderiv ℝ (⇑f) x).det ≠ 0 := sorry
  -- Choose some point x₀ ∈ s ⊆ H.
  --inhabit H -- by_cases empty_or_inhabited, or something
  --let x₀ := inhabited_h.default
  let x₀ : s := sorry
  obtain ⟨x₀, hx₀⟩ := x₀
  set detx₀ := (fderiv ℝ (⇑f) x₀).det
  by_cases h: 0 < detx₀
  · left
    intro x hx
    -- Choose a path `γ` connecting x and x₀.
    obtain ⟨γ, hγ⟩ := hs'.joinedIn x₀ hx₀ x hx
    -- Consider the function `t ↦ det (fderiv f γ(t))`.
    let g := fun t ↦ (fderiv ℝ f (γ t)).det
    have hneq (t) : g t ≠ 0 := by apply this
    have : 0 < g 0 := by simp only [Path.source, g, h]
    rw [← Path.target γ]
    show 0 < g 1
    by_contra h'
    push_neg at h'
    have : g 1 < 0 := lt_of_le_of_ne h' (hneq 1)
    -- intermediate value theorem!
    -- xxx: better to extend these to all of ℝ, with a junk value; a fight for another day!
    have aux : IsPreconnected unitInterval := sorry--let pr := hs.isPreconnected
    let ivt := aux.intermediate_value₂ (a := 0) (b := 1) (g := fun _ → 0) --(hg := continuousOn_const)--hx₀ hx
    let ivt' := ivt (g := fun _ ↦ 0)
    have : ConditionallyCompleteLinearOrder ↑unitInterval := sorry
    haveI : OrderTopology ↑unitInterval := sorry
    let ivt := intermediate_value_Icc (f := g)

    --have : (fderiv ℝ f )
    -- use path-connectedness and continuity of the determinant, and the intermediate value theorem
    sorry
  · have : detx₀ < 0 := by
      by_contra h'
      push_neg at h'
      exact h (lt_of_le_of_ne h' (this x₀).symm)
    right
    intro x hx
    sorry -- use an analogous argument as above


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

/-! ### Orientable manifolds -/
section OrientableManifold

/-- Typeclass defining orientable manifolds. -/
class OrientableManifold (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M] extends
  HasGroupoid M (@orientationPreservingGroupoid H _ _ _) : Prop

/-- `0`-dimensional manifolds are always orientable. -/
lemma orientableManifold_of_zero_dim (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (h : FiniteDimensional.finrank ℝ H = 0) : OrientableManifold H M where
  compatible := fun _ _ ↦
    ⟨orientationPreserving_of_zero_dim _ _ h, orientationPreserving_of_zero_dim _ _ h⟩

/-- Typeclass defining orientable smooth manifolds. -/
class OrientableSmoothManifold (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ E H) extends
  HasGroupoid M ((contDiffGroupoid ⊤ I) ⊓ orientationPreservingGroupoid) : Prop

end OrientableManifold

/-- A finite-dimensional normed space is an orientable smooth manifold. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : ModelWithCorners ℝ E E} : OrientableSmoothManifold E (I := I) :=
  { hasGroupoid_model_space _ _ with }
