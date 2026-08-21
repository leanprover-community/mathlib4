/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import Mathlib.Geometry.Manifold.Notation

/-! ### The covariant Hessian -/

public noncomputable section

open Bundle
open scoped Manifold
section Hessian

-- Standard Manifold and Bundle Setup
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → _) I]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]

variable [(x : M) → AddCommGroup (V x)] [(x : M) → Module 𝕜 (V x)]
variable [(x : M) → TopologicalSpace (V x)]
variable [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
variable [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

-- The connections
variable (covV : CovariantDerivative I F V)
variable (covTM : CovariantDerivative I E (TangentSpace I : M → _))

variable (σ : Π x, V x) (x : M)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The covariant Hessian of a section `σ` evaluated at point `x`.
    This provides the rigorous bilinear map `TM_x →L[𝕜] TM_x →L[𝕜] V_x` representing `∇²σ`. -/
def covariantHessian : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  -- The first covariant derivative ∇σ is a global section of the Hom-bundle Hom(TM, V)
  let nabla_sigma : Π y : M, TangentSpace I y →L[𝕜] V y := fun y ↦ covV σ y
  -- The covariant Hessian is the Hom-bundle connection applied to ∇σ at point x
  covTM.homBundle covV nabla_sigma x

omit [ContMDiffVectorBundle 1 F V I] in
/-- The defining formula for the covariant Hessian: `∇²σ (X, Y) = ∇_X (∇_Y σ) - ∇_{∇_X Y} σ`,
valid whenever `∇σ` is a differentiable section of `Hom(TM, V)` at `x` and `Y` is a vector field
which is differentiable at `x`. -/
lemma covariantHessian_apply (hσ : MDiffAt T% (covV σ) x)
    (X : TangentSpace I x) {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) :
    covariantHessian covV covTM σ x X (Y x)
      = covV (fun y ↦ covV σ y (Y y)) x X - covV σ x (covTM Y x X) :=
  -- homBundlePointwise_apply covTM covV hσ X hY
  sorry

end Hessian

#min_imports
