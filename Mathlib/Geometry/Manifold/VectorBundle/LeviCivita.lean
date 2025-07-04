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
variable [IsManifold I ∞ M]
--variable (cov : CovariantDerivative I E (V := TangentBundle I M))
-- TODO: state "cov is a connection on TM" in a way that type-checks...
-- (cov : CovariantDerivative I E (V := fun x ↦ TangentSpace I x)) does not...

include I in
variable (Y Z) in
noncomputable def lhs_aux : M → ℝ := fun x ↦ ⟪Y x, Z x⟫

variable (X Y Z) in
noncomputable def lhs : M → ℝ := fun x ↦ mfderiv I 𝓘(ℝ) (lhs_aux I Y Z) x (X x)

-- variable (X Y Z) in
-- noncomputable def rhs : M → ℝ := ⟪cov X Y, Z⟫ + ⟪Y, cov X Z⟫

/-

def CovariantDerivative.IsCompatible (cov) (g) : lhs = rhs on mdiff. functions

new definition
IsLeviCivitaConnection: IsCompatible \and IsTorsionFree

uniqueness theorem: any two Levi-Civita connections agree on all mdiff vector fields
(probably not everywhere, as addition rules don't apply to them?)

-----> helper lemmas
on a metric vector bundle: orthonormal frame (continuous setting at first),
prove these are continuous
(and smooth if the metric is smooth)

lemma: <X, Y> = <X', Y> for all Y implies X and X' are equal
(-> use for uniqueness of LC connection)

compute: a symmetric connection satisfies xxx
  a LC connection satisfies ...
  deduce the final equation characterising it

corollary: uniqueness

-- A choice of Levi-Civita connection on TM: this is unique up to the value on non-differentiable vector fields.
-- If you know the Levi-Civita connection already, you can use IsLeviCivitaConnection instead.
def LeviCivitaConnection := sorry

this is the existence part, I presume

lemma : IsLeviCivitaConnection (LeviCivitaConnection) := sorry

-/
