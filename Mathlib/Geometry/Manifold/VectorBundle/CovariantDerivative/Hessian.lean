/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom

/-!
# Hessian

...
-/

open Bundle
open scoped Manifold

public noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

-- Base manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → _) I]

-- Fiber bundle
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

-- Covariant derivatives and the tangent bundle and on the fiber bundle V
variable (covTM : CovariantDerivative I E (TangentSpace I : M → _))
  (cov : CovariantDerivative I F V)

-- Section of the bundle V
variable (v : (x : M) → V x)

namespace CovariantDerivative

/-- Covariant Hessian acting on a section `v` of a vector bundle `V`. -/
def hessian (x : M) : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  (covTM.homBundle cov) (cov v) x

theorem hessian_apply_eq_extend {x : M} (hv : MDiffAt T% (cov v) x)
  (X Y : TangentSpace I x) : hessian covTM cov v x X Y =
  (cov (fun y ↦ (cov v y) (FiberBundle.extend E Y y)) x) X
    - (cov v x) ((covTM (FiberBundle.extend E Y) x) X) := by
  simp_all [hessian, covTM.homBundle_apply_eq_extend cov]

end CovariantDerivative
