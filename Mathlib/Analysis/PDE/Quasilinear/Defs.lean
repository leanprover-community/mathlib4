/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # First Order Quasilinear PDEs

This file develops some basic theory of first order quasilinear PDEs.

## Main definitions

- `FirstOrderQuasiLinearPDE 𝕜 V`: the type of quasilinear PDEs on a `𝕜` vector space `V`, i.e.
  equations in a variable `u : V → 𝕜` of the form `E : (∂u) a = c` where `∂u` denotes the
  _Frechet derivative_ of `u`, `a : V × 𝕜 → V` is the _vector of coefficients_ of `E` and
  `c : V × 𝕜 → 𝕜` is the _constant term_ of `E`. When `V` is equipped with a set of standard
  coordinates `x₁, ..., xₙ`, this simplifies to the more familiar form `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c`
  where `a(x, U) = (a₁(x, U),...,aₙ(x, U))` and `∂ᵢ` is the partial derivative with respect to
  the `i`-th standard coordinate.

- `E.regularBy P`: the predicate that the coefficients and constant term of the equation
  `E` satisfy some regularity condition `P`. Typically, `P` will be `ContDiff 𝕜 n`
  or something similar.

- `E.hasSolutionAt u x`: the predicate that the function `u` is a solution to the equation at
  point `x`.

- `E.HasCharacteristicAt γ t₀`: the predicate that a curve `γ : 𝕜 → V × 𝕜` satisfies the relation
  `γ'(t) = (a(γ(t)), c(γ(t)))` at time `t = t₀`, where `a` is the vector of coefficients of equation
  `E`, and `c` is the constant term.

-/

open Set

open scoped Topology

variable {𝕜 V : Type*}

noncomputable section

open scoped Topology

variable (𝕜 V) in
/-- `FirstOrderQuasiLinearPDE 𝕜 V` is the type of quasilinear PDEs on a `𝕜` vector space `V`.

Note: we need to consider functions defined on `V × ℝ` since in general the coefficients of a quasilinear
PDE `a₁ ∂₁u + ... + aₙ ∂ₙu = c` might depend on the function `u : V → ℝ`.
-/
@[ext]
structure FirstOrderQuasiLinearPDE where
  /-- The vector of coefficients `a` of the equation.

  When encoding equation `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` in an unknown function `u`,
  with coefficients `aᵢ` and constant term `c` that depend on `x` and `u`,
  `coeff (x, U)` corresponds to the vector `(a₁(x, U), ..., aₙ(x, U))`. Here, `U` is
  a variable that encodes the dependence of the coefficients on the unknown function `u`,
  and `x = (x₁, ..., xₙ)` is the variable on which `u` depends.
  -/
  coeff : V × 𝕜 → V
  /-- The constant term `c` of the equation.

  When encoding equation `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` in an unknown function `u`,
  with coefficients `aᵢ` and constant term `c` that depend on `x` and `u`,
  `const (x, U)` corresponds to the constant term `c(x, U)`. Here, `U` is
  a variable that encodes the dependence of the constant term on the unknown function `u`,
  and `x = (x₁, ..., xₙ)` is the variable on which `u` depends.
  -/
  const : V × 𝕜 → 𝕜

/-- `E.RegularBy` is the predicate that the coefficients of `E` satisfy the regularity condition `P`.
Typically, we would take `P = ContDiff` or so on. -/
class FirstOrderQuasiLinearPDE.RegularBy (E : FirstOrderQuasiLinearPDE 𝕜 V) (P : (V × 𝕜 → V × 𝕜) → Prop) where
  reg : P (fun x => (E.coeff x, E.const x)) := by fun_prop

end

namespace FirstOrderQuasiLinearPDE

section Notation

@[inherit_doc FirstOrderQuasiLinearPDE.coeff]
scoped notation "a[" E "]" => FirstOrderQuasiLinearPDE.coeff E

@[inherit_doc FirstOrderQuasiLinearPDE.const]
scoped notation "c[" E "]" => FirstOrderQuasiLinearPDE.const E

end Notation

section Solutions

variable (E : FirstOrderQuasiLinearPDE 𝕜 V)
variable [AddCommGroup V] [TopologicalSpace V]
variable [NontriviallyNormedField 𝕜] [Module 𝕜 V]


/-- `E.hasSolutionAt u x` is the predicate that the function `u` is a solution to the PDE at point `E`.

Note that we don't place any differentiability requirements. -/
def HasSolutionAt (u : V → 𝕜) (x : V) : Prop :=
  --In the future, I think we should include some weaker versions of this,
  --e.g. `IsSolutionWithinAt` and so on. The main theorem about characteristics
  --should be provable with weaker conditions.
  ∃ u' : V →L[𝕜] 𝕜, HasFDerivAt u u' x ∧ u' (a[E] (x, u x)) = c[E] (x, u x)

end Solutions


section Characteristics

section

variable (E : FirstOrderQuasiLinearPDE 𝕜 V)
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [Module 𝕜 V] [ContinuousSMul 𝕜 V]

/-- The predicate that a curve `γ = (X, U) : ℝ → V × ℝ` is a characteristic curve for PDE `E`,
at time `t₀` i.e. `d/dt X(t₀) = a(X(t), U(t))` and `d/dt U(t₀) = c(X(t), U(t))` -/
def HasCharacteristicAt (γ : 𝕜 → V × 𝕜) (t₀ : 𝕜) : Prop :=
  HasDerivAt γ (a[E] (γ t₀), c[E] (γ t₀)) t₀

end

section

variable {E : FirstOrderQuasiLinearPDE 𝕜 V}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

lemma differentiableAt_of_hasSolutionAt {u : V → 𝕜} {x : V}
    (H : E.HasSolutionAt u x) : DifferentiableAt 𝕜 u x := by
  obtain ⟨u', hu', _⟩ := H
  exact hu'.differentiableAt

lemma fderiv_apply_of_hasSolutionAt {u : V → 𝕜} {x : V}
    (H : E.HasSolutionAt u x) : fderiv 𝕜 u x (a[E] (x, u x)) = c[E] (x, u x) := by
  obtain ⟨u', hu', hu''⟩ := H
  rwa [HasFDerivAt.fderiv hu']

end
