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

open scoped Manifold

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

lemma abstract2a {f : unitInterval → ℝ} (hf : Continuous f) (hf' : ∀ t, f t ≠ 0)
    {x : unitInterval} (hx : f x > 0) : ∀ t, f t > 0 := by
  by_contra! h
  obtain ⟨t, ht⟩ := h
  obtain ⟨x, _, hx⟩ := isPreconnected_univ.intermediate_value₂
    (a := t) (b := x) (by tauto) (by tauto)
    (hf.continuousOn (s := Set.univ)) (continuous_const (y := 0).continuousOn (s := Set.univ))
    ht hx.le
  exact (hf' x) hx

lemma abstract2b {f : unitInterval → ℝ} (hf : Continuous f) (hf' : ∀ t, f t ≠ 0)
    {x : unitInterval} (hx : f x < 0) : ∀ t, f t < 0 := by
  by_contra! h
  obtain ⟨t, ht⟩ := h
  obtain ⟨x, _, hx⟩ := isPreconnected_univ.intermediate_value₂
    (a := x) (b := t) (by tauto) (by tauto)
    (hf.continuousOn (s := Set.univ)) (continuous_const (y := 0).continuousOn (s := Set.univ))
    hx.le ht
  exact (hf' x) hx

-- Not quite what I want below, but a similar sketch.
lemma abstract1 {f : unitInterval → ℝ} (hf : Continuous f) (hf' : ∀ t, f t ≠ 0) :
    (∀ t, f t > 0) ∨ (∀ t, f t < 0) := by
  let x₀ : unitInterval := 0
  by_cases h : f x₀ > 0
  · left
    exact fun x ↦ abstract2a hf hf' h x
  · right
    push_neg at h
    exact fun x ↦ abstract2b hf hf' (lt_of_le_of_ne h (hf' x₀)) x

/-- A linear isomorphism on a connected set is
either orientation-preserving or orientation-reversing. -/
lemma foo (f : H ≃L[ℝ] H) {s : Set H} (hs : IsConnected s) (hs' : IsPathConnected s) :
    OrientationPreserving f s ∨ OrientationReversing f s := by
  -- At each point, its determinant is non-zero, as it is a diffeomorphism.
  -- The most general proof proceeds via local diffeomorphism,
  -- and deducing the linear isomorphisms are diffeomorphisms are local diffeomorphisms...
  have h₁ (x : H) : (fderiv ℝ (⇑f) x).det ≠ 0 := sorry
  by_cases hyp: Nonempty s
  swap
  · left
    intro _ hx
    apply False.elim
    tauto
  -- Choose some point x₀ ∈ s ⊆ H. TODO!
  let x₀ : s := sorry -- inhabited_h.default
  obtain ⟨x₀, hx₀⟩ := x₀
  by_cases h: 0 < (fderiv ℝ (⇑f) x₀).det
  · left
    intro x hx
    -- Choose a path `γ` connecting x and x₀,
    -- and consider the function `g: t ↦ det (fderiv f γ(t))`.
    obtain ⟨γ, hγ⟩ := hs'.joinedIn x₀ hx₀ x hx
    let g := fun t ↦ (fderiv ℝ f (γ t)).det
    have aux : Continuous fun t ↦ (fderiv ℝ f (γ t)) :=
      Continuous.comp (f.contDiff.continuous_fderiv (OrderTop.le_top 1)) γ.continuous
    have hg : Continuous g := (ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := H)).comp aux
    rw [← Path.target γ]
    exact abstract2a hg (by simp [h₁]) (x := 0) (by simp only [g, Path.source, h]) 1
  · right
    intro x hx
    obtain ⟨γ, hγ⟩ := hs'.joinedIn x₀ hx₀ x hx
    let g := fun t ↦ (fderiv ℝ f (γ t)).det
    have aux : Continuous fun t ↦ (fderiv ℝ f (γ t)) :=
      Continuous.comp (f.contDiff.continuous_fderiv (OrderTop.le_top 1)) γ.continuous
    have hg : Continuous g := (ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := H)).comp aux

    have h' : (fderiv ℝ (⇑f) x₀).det < 0 := by
      by_contra! h'
      exact h (lt_of_le_of_ne h' (h₁ x₀).symm)
    have h₀ : g 0 < 0 := by simp only [g, Path.source, h']
    rw [← Path.target γ]
    exact abstract2b hg (by simp [h₁]) h₀ 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]

open Set
/-- The pregroupoid of orientation-preserving maps. -/
def orientationPreservingPregroupoid [FiniteDimensional ℝ E] : Pregroupoid H where
  property f s := OrientationPreserving (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I))
  -- XXX: should this condition be added?
  -- ∧ (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
  comp {f} {g} U V hf hg hU hV hUV x hx := by
    have hx' : x ∈ I.symm ⁻¹' U ∩ interior (range I) ∩
        I ∘ f ∘ I.symm ⁻¹' (I.symm ⁻¹' V ∩ interior (range I)) := by
      obtain ⟨hx1, hx2⟩ := hx
      constructor
      · exact ⟨mem_of_mem_inter_left hx1, hx2⟩
      · refine ⟨by simp_all, ?_⟩
        sorry -- XXX: does this require the xxx condition above?
    convert orientationPreserving_comp hf hg x hx'
    simp [Function.comp]
  id_mem := by
    dsimp
    rw [univ_inter]
    have aux := I.rightInvOn
    -- by aux, I ∘ I.symm agree with id on range I,
    -- so it suffices to show id is or-pres there (that's a congr lemma!)
    convert orientationPreserving_id _
    sorry
  locality {f u} _ h x hxu := by
    have ⟨v, _, hxv, h⟩ := h (I.symm x) hxu.1
    exact h _ ⟨Set.mem_inter hxu.1 hxv, hxu.2⟩
  congr {f g u} hu fg hf x hx := by
    sorry --rw [(Filter.eventuallyEq_of_mem (hu.mem_nhds hx) fg).fderiv_eq]
    --exact hf x hx

/-- The groupoid of orientation-preserving maps. -/
def orientationPreservingGroupoid [FiniteDimensional ℝ E] : StructureGroupoid H :=
  (orientationPreservingPregroupoid I).groupoid

/-- The groupoid of orientation-preserving `n` times continuously differentiable maps -/
def contDiffOrientationPreservingGroupoid (n : ℕ∞) (I : ModelWithCorners ℝ E H)
    [FiniteDimensional ℝ E] : StructureGroupoid H :=
  (orientationPreservingGroupoid I) ⊓ (contDiffGroupoid n I)

end OrientationPreserving

/-! ### Orientable manifolds -/
section OrientableManifold

/-- Typeclass defining orientable manifolds: a finite-dimensional (topological) manifold
is orientable if and only if it admits an orientable atlas. -/
class OrientableManifold {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] extends
  HasGroupoid M (orientationPreservingGroupoid I) : Prop

/-- `0`-dimensional manifolds are always orientable. -/
lemma orientableManifold_of_zero_dim {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] (h : FiniteDimensional.finrank ℝ E = 0) :
    OrientableManifold M I where
  compatible := fun _ _ ↦
    ⟨orientationPreserving_of_zero_dim _ _ h, orientationPreserving_of_zero_dim _ _ h⟩

/-- Typeclass defining orientable smooth manifolds: a smooth manifold is orientable
if and only if it admits an atlas which is both smooth and orientable -/
class OrientableSmoothManifold {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] extends
  HasGroupoid M (contDiffOrientationPreservingGroupoid ⊤ I) : Prop

end OrientableManifold

/-- A finite-dimensional normed space is an orientable smooth manifold. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : ModelWithCorners ℝ E E} : OrientableSmoothManifold E (I := I) :=
  { hasGroupoid_model_space _ _ with }
