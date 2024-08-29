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

* `OrientationPreserving` : a map is orientation-preserving on a given set if the determinant of
  its Jacobian is strictly positive on that set.
* `orientationPreservingGroupoid` : the groupoid of partial homeos of `H` which are
  orientation-preserving.
* `OrientableManifold`: a type class saying that the charted space `M`, modelled on the space `H`,
  admis an orientation. This type class is just a shortcut for `HasGroupoid M
  (@orientationPreservingGroupoid H _ _)`.

-/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section orientationPreservingGroupoid

/--
A map is orientation-preserving on a given set if it is differentiable and the determinant of its
Jacobian is strictly positive on that set.
-/
def OrientationPreserving (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, DifferentiableAt ℝ f x ∧ 0 < (fderiv ℝ f x).det

/-- The pregroupoid of orientation-preserving maps. -/
def orientationPreservingPregroupoid : Pregroupoid H where
  property f s := OrientationPreserving f s
  comp {f g u v} hf hg _ _ _ := by
    intro x ⟨hxu, hxv⟩
    rw [fderiv.comp _ (hg (f x) hxv).1 (hf x hxu).1]
    have h₁ : 0 < (fderiv ℝ f x).det := (hf x hxu).2
    have h₂ : 0 < (fderiv ℝ g (f x)).det := (hg (f x) hxv).2
    unfold ContinuousLinearMap.det ContinuousLinearMap.comp
    rw [(fderiv ℝ g (f x)).toLinearMap.det_comp (fderiv ℝ f x).toLinearMap]
    exact ⟨(hg (f x) hxv).1.comp x (hf x hxu).1, mul_pos h₂ h₁⟩
  id_mem := by
    intro x _
    simp only [Set.mem_univ, differentiableAt_id, fderiv_id, true_and]
    rw [ContinuousLinearMap.id, ContinuousLinearMap.det, LinearMap.det_id]
    exact zero_lt_one
  locality {f u} _ h x hxu :=
    have ⟨v, _, hxv, h⟩ := h x hxu
    h x <| Set.mem_inter hxu hxv
  congr {f g u} hu fg hf := by
    intro x hx
    have := Filter.eventuallyEq_of_mem (IsOpen.mem_nhds hu hx) fg
    apply And.intro
    · rw [this.differentiableAt_iff]
      exact (hf x hx).1
    · rw [this.fderiv_eq]
      exact (hf x hx).2

/-- The groupoid of orientation-preserving maps. -/
def orientationPreservingGroupoid : StructureGroupoid H :=
  orientationPreservingPregroupoid.groupoid

end orientationPreservingGroupoid

section OrientableManifold

/-- Typeclass defining orientable manifolds. -/
class OrientableManifold (M : Type*) [TopologicalSpace M] [ChartedSpace H M] extends
  HasGroupoid M (@orientationPreservingGroupoid H _ _) : Prop

end OrientableManifold
