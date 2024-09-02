/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Orientable Manifolds

This module defines orientable manifolds.

## Main Definitions

- `OrientationPreserving` : a map is orientation-preserving on a given set if the determinant of
  its Jacobian is strictly positive on that set.
- `orientationPreservingGroupoid` : the groupoid of partial homeos of `H` which are
  orientation-preserving.
- `OrientableManifold`: a type class saying that the charted space `M`, modelled on the space `H`,
  admis an orientation.

## TODO

- Define orientable `0`-manifolds.

-/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section OrientationPreserving

/--
A map is orientation-preserving on a given set if it is differentiable and the determinant of its
Jacobian is strictly positive on that set.
-/
def OrientationPreserving (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, 0 < (fderiv ℝ f x).det

/--
A map is orientation-reversing on a given set if it is differentiable and the determinant of its
Jacobian is strictly negative on that set.
-/
def OrientationReversing (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, (fderiv ℝ f x).det < 0

lemma OrientationPreserving.DifferentiableAt [Nontrivial H] [FiniteDimensional ℝ H] {f : H → H}
  {s : Set H} (h : OrientationPreserving f s) : ∀ x ∈ s, DifferentiableAt ℝ f x := by
  unfold OrientationPreserving at h
  contrapose! h
  obtain ⟨x, hx, hd⟩ := h
  use x, hx
  rw [fderiv_zero_of_not_differentiableAt hd, ContinuousLinearMap.det]
  simp [ne_of_gt FiniteDimensional.finrank_pos]

lemma OrientationReversing.DifferentiableAt [Nontrivial H] [FiniteDimensional ℝ H] {f : H → H}
  {s : Set H} (h : OrientationReversing f s) : ∀ x ∈ s, DifferentiableAt ℝ f x := by
  unfold OrientationReversing at h
  contrapose! h
  obtain ⟨x, hx, hd⟩ := h
  use x, hx
  rw [fderiv_zero_of_not_differentiableAt hd, ContinuousLinearMap.det]
  simp [ne_of_gt FiniteDimensional.finrank_pos]

lemma orientationPreserving_id (s : Set H) : OrientationPreserving id s := by
  intro
  simp [ContinuousLinearMap.det]

lemma orientationPreserving_comp [Nontrivial H] [FiniteDimensional ℝ H] {f g : H → H} {u v : Set H}
    (hf : OrientationPreserving f u) (hg : OrientationPreserving g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.DifferentiableAt (f x) hxv) (hf.DifferentiableAt x hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_pos (hg (f x) hxv) (hf x hxu)

lemma orientationPreserving_comp_orientationReversing [Nontrivial H] [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationPreserving f u) (hg : OrientationReversing g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.DifferentiableAt (f x) hxv) (hf.DifferentiableAt x hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_neg_of_neg_of_pos (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp_orientationPreserving [Nontrivial H] [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationReversing f u) (hg : OrientationPreserving g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.DifferentiableAt (f x) hxv) (hf.DifferentiableAt x hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_neg_of_pos_of_neg (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp [Nontrivial H] [FiniteDimensional ℝ H] {f g : H → H} {u v : Set H}
    (hf : OrientationReversing f u) (hg : OrientationReversing g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.DifferentiableAt (f x) hxv) (hf.DifferentiableAt x hxu)]
  unfold ContinuousLinearMap.det ContinuousLinearMap.comp
  rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
  exact mul_pos_of_neg_of_neg (hg (f x) hxv) (hf x hxu)

/-- The pregroupoid of orientation-preserving maps. -/
def orientationPreservingPregroupoid [Nontrivial H] [FiniteDimensional ℝ H] : Pregroupoid H where
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
def orientationPreservingGroupoid [Nontrivial H] [FiniteDimensional ℝ H] : StructureGroupoid H :=
  orientationPreservingPregroupoid.groupoid

end OrientationPreserving

section OrientableManifold

/-- Typeclass defining orientable manifolds. -/
class OrientableManifold [Nontrivial H] [FiniteDimensional ℝ H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] extends
  HasGroupoid M (@orientationPreservingGroupoid H _ _ _ _) : Prop

end OrientableManifold
