/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani, Michael Rothgang
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
- `orientableManifold_of_zero_dim` : `0`-dimensional manifolds are always orientable.
- A finite-dimensional normed space is orientable (w.r.t. the trivial model).

## TODO

- Generalize this discussion to other fields, for example over `ℚ`.
- On a given connected set, a diffeomorphism is either orientation preserving or orientation
  reversing.
- A real interval `Icc x y` is orientableA normed space (with the trivial model) is orientable.
- The `n`-sphere is orientable.
- Products of orientable manifolds are orientable.
- Define orientations of a smooth manifold, and show that a manifold is orientable if and only if it
  admits an orientation.
- Define orientation preserving and reversing maps between manifolds.

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
  simpa only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    using mul_pos (hg (f x) hxv) (hf x hxu)

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
  simpa only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    using mul_pos_of_neg_of_neg (hg (f x) hxv) (hf x hxu)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]

open Set

/-- The pregroupoid of orientation-preserving maps. -/
def orientationPreservingPregroupoid [FiniteDimensional ℝ E] : Pregroupoid H where
  property f s :=
    OrientationPreserving (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I))
    -- This second condition basically says "on `s`, `f` maps the interior of `M`
    -- to the interior of `M`: this can be proven superfluous in many contexts,
    -- but such a proof is currently out of reach for mathlib.
    -- Hence, we add this condition.
    ∧ (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
  comp {f g} U V hf hg hU hV hUV := by
    refine ⟨fun x ⟨hx₁, hx₂⟩ ↦ ?_, fun y ⟨x, hx, _⟩ ↦ ?_⟩
    · have hx' : x ∈ I.symm ⁻¹' U ∩ interior (range I) ∩
          I ∘ f ∘ I.symm ⁻¹' (I.symm ⁻¹' V ∩ interior (range I)) :=
        ⟨⟨mem_of_mem_inter_left hx₁, hx₂⟩, by simp_all, by aesop⟩
      convert orientationPreserving_comp hf.1 hg.1 x hx'
      simp [Function.comp]
    · have : x ∈ I.symm ⁻¹' U ∩ interior (range I) :=
        ⟨mem_of_mem_inter_left (mem_of_mem_inter_left hx), mem_of_mem_inter_right hx⟩
      have : I (f (I.symm x)) ∈ I.symm ⁻¹' V ∩ interior (range I) :=
        ⟨by simp_all, hf.2 <| mem_image_of_mem (↑I ∘ f ∘ ↑I.symm) this⟩
      apply hg.2
      aesop
  id_mem := by
    dsimp
    constructor
    · have h_fderiv : ∀ x ∈ interior (range I), fderiv ℝ (I ∘ I.symm) x = fderiv ℝ id x := by
        intro x hx
        apply Filter.EventuallyEq.fderiv_eq
        exact Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp hx) (by simp)
      exact univ_inter _ ▸ fun x hx ↦ h_fderiv x hx ▸ orientationPreserving_id _ x hx
    · rw [univ_inter]
      rintro x ⟨x', hx', hx''⟩
      have : x = x' := hx'' ▸ I.right_inv (interior_subset hx')
      exact this ▸ hx'
  locality {f u} _ h :=
    And.intro
    (fun x hxu ↦ have ⟨v, _, hxv, h⟩ := h (I.symm x) hxu.1
    h.1 _ ⟨Set.mem_inter hxu.1 hxv, hxu.2⟩)
    (fun _ ⟨x, ⟨aux, hxint⟩, hx⟩ ↦ have ⟨v, _, hxv, ⟨_, hint⟩⟩ := h (I.symm x) aux
    hx ▸ hint (mem_image_of_mem (↑I ∘ f ∘ ↑I.symm) ⟨⟨aux, hxv⟩, hxint⟩))
  congr {f g u} hu fg hf := by
    apply And.intro
    · intro x hx
      have : ∀ x ∈ I.symm ⁻¹' u ∩ interior (range ↑I), (I ∘ g ∘ I.symm) x = (I ∘ f ∘ I.symm) x := by
        simp_all
      have : fderivWithin ℝ (↑I ∘ g ∘ ↑I.symm) (I.symm ⁻¹' u ∩ interior (range ↑I)) x
          = fderivWithin ℝ (↑I ∘ f ∘ ↑I.symm) (I.symm ⁻¹' u ∩ interior (range ↑I)) x :=
        fderivWithin_congr' this hx
      have : fderiv ℝ (↑I ∘ g ∘ ↑I.symm) x = fderiv ℝ (↑I ∘ f ∘ ↑I.symm) x := by
        rw [fderivWithin_of_isOpen, fderivWithin_of_isOpen] at this
        exact this
        rw [Set.inter_comm]
        apply ContinuousOn.isOpen_inter_preimage
        · exact ModelWithCorners.continuousOn_symm I
        · exact isOpen_interior
        exact hu
        exact hx
        rw [Set.inter_comm]
        apply ContinuousOn.isOpen_inter_preimage
        · exact ModelWithCorners.continuousOn_symm I
        · exact isOpen_interior
        exact hu
        exact hx
      exact this ▸ hf.1 x hx
    · sorry

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
  compatible := sorry /- fun _ _ _ ↦
    ⟨orientationPreserving_of_zero_dim _ _ h, orientationPreserving_of_zero_dim _ _ h⟩ -/

/-- Typeclass defining orientable smooth manifolds: a smooth manifold is orientable
if and only if it admits an atlas which is both smooth and orientable -/
class OrientableSmoothManifold {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] extends
  HasGroupoid M (contDiffOrientationPreservingGroupoid ⊤ I) : Prop

/-- A finite-dimensional normed space is an orientable smooth manifold. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : ModelWithCorners ℝ E E} : OrientableSmoothManifold E (I := I) :=
  { hasGroupoid_model_space _ _ with }

end OrientableManifold
