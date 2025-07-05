/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# The Levi-Civita connection

This file will define the Levi-Civita connection on any Riemannian manifold.
Details to be written!

-/

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

-- Let M be a C^k real manifold modeled on (E, H), endowed with a Riemannian metric.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  -- comes in a future PR by sgouezel; don't need this part yet
  -- [IsRiemannianManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! Compatible connections: a connection on TM is compatible with the metric on M iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all vector fields X, Y and Z on `M`.
The left hand side is the differential of the function ⟨Y, Z⟩ along the vector field X:
at each point p, let γ(t) be a curve representing the tangent vector X p,
then the LHS is the initial derivative of the function t ↦ ⟨Y(γ(p)), Z(γ p)⟩ at 0. -/

variable {X Y Z W : Π x : M, TangentSpace I x}

-- /-- The scalar product of two vector fields -/
-- noncomputable def product (X Y : Π x : M, TangentSpace I x) : M → ℝ := fun x ↦ ⟪X x, Y x⟫
-- smoothness results shown in Riemannian.lean: will omit

-- TODO: state "cov is a connection on TM" in a way that type-checks...
-- (cov : CovariantDerivative I E (V := fun x ↦ TangentSpace I x)) does not...

variable {I} in
def Xcurve (x : M) : ℝ → M := sorry -- TODO: include X also!

lemma Xcurve_zero (x : M) : Xcurve x 0 = x := sorry -- will be rfl

-- tangent vector X x equals the differential of Xcurve; not sure how to say this best!
-- lemma Xcurve_diff (x : M) : X x = ... := sorry

variable {I} (X Y Z) in
noncomputable def asdf (x : M) : ℝ → ℝ := (fun t ↦ ⟪Y (Xcurve x t), Z (Xcurve x t)⟫)

variable (X Y Z) in
noncomputable def lhs : M → ℝ := fun x ↦ deriv (asdf Y Z x) 0

-- variable (X Y Z) in
-- noncomputable def rhs : M → ℝ := ⟪cov X Y, Z⟫ + ⟪Y, cov X Z⟫
