/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! # Metric connections

This file defines connections on a Riemannian vector bundle which are compatible with the ambient
metric. A bundled connection `∇` on a Riemannian vector bundle `(V, g)` is compatible with the
metric `g` if and only if the differentiated metric tensor `∇ g` (defined by
`(X, σ, τ) ↦ 𝓛_X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)`) vanishes on all differentiable vector fields
`X` and differentiable sections `σ`, `τ`.

## Main definitions and results

* `CovariantDerivative.derivMetricTensor`: the tensor
  `(X, σ, τ) ↦ 𝓛_X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)` defining when a connection `∇` on a
  Riemannian vector bundle `(V, g)` is compatible with the metric `g`.
* `CovariantDerivative.derivMetricTensor_apply` and
  `CovariantDerivative.derivMetricTensor_apply_eq_extend` give formulas for applying
  the compatibility tensor at `x` to vector fields and sections which are differentiable at `x`,
  resp. to extensions of tangent vectors and sections at `x` to differentiable vector fields and
  sections near `x`.
* `CovariantDerivative.IsMetricCompatible`: predicate for a connection to be metric, namely that
  `∇` is metric iff its `derivMetricTensor` vanishes

## TODO

* When Mathlib has a notion of parallel transport, prove the equivalence of
 `CovariantDerivative.IsMetricCompatible` with the characterisation that parallel transport be an
  isometry.

* Given connections on bundles `V` and `W`, there is an induced connnection on the bundle
  `Hom(V, W)`. When this induced connection has been defined in Mathlib, rephrase the definition of
  `CovariantDerivative.derivMetricTensor`, to be simply the covariant derivative of the
  metric tensor (considered as a section of `Hom(V, Hom(V, ℝ))`).

-/
open Bundle NormedSpace
open scoped Manifold ContDiff

variable
  -- Let `M` be a real manifold modeled on `(E, H)`
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Let `V` be a bundle over `M` with standard fiber `F`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V]

/-! # Compatible connections

A connection on `V` is compatible with the metric on `V` iff `𝓛_X ⟨σ, τ⟩ = ⟨∇_X σ, τ⟩ + ⟨σ, ∇_X τ⟩`
holds for all sufficiently nice vector fields `X` on `M` and sections `σ`, `τ` of `V`.
The left hand side is the Lie derivative of the function `⟨σ, τ⟩` w.r.t. the vector field `X`:
its value at `x` is `df(X x)`, where `f := ⟨σ, τ⟩` (ie. `X` is seen a derivation on the algebra
of functions on the base manifold acting on the function `⟨σ, τ⟩`).
In our definition, we ask for this identity to hold at each `x : M`, whenever `X`, `σ` and `τ` are
differentiable at `x`.
-/

variable {σ σ' σ'' τ τ' τ'' : Π x : M, V x}

local notation "⟪" σ ", " τ "⟫" => fun x ↦ inner ℝ (σ x) (τ x)

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `V`.
variable (cov : CovariantDerivative I F V)

/-- Local notation for a covariant derivative on a vector bundle acting on a vector field and a
section. -/
local syntax "∇" term:arg term : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))

/-- The function defining the compatibility tensor for `∇` w.r.t. `g`:
prefer using `derivMetricTensor` instead -/
noncomputable def derivMetricTensorAux (σ τ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  d% ⟪σ, τ⟫ x - innerSL ℝ (τ x) ∘L cov σ x - innerSL ℝ (σ x) ∘L cov τ x

@[simp]
lemma derivMetricTensorAux_apply (σ τ : Π x : M, V x) {x : M} (X₀ : TangentSpace I x) :
    derivMetricTensorAux I cov σ τ x X₀ =
      d% ⟪σ, τ⟫ x X₀ - inner ℝ (cov σ x X₀) (τ x) - inner ℝ (σ x) (cov τ x X₀) := by
  rw [real_inner_comm]
  rfl

-- From now on, assume `V` is a vector bundle endowed with a `C¹` Riemannian metric.
variable [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {x : M}

theorem tensorial_derivMetricTensorAux₁ (τ : Π x, V x) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I F (derivMetricTensorAux I cov · τ x) x where
  smul hf hσ := by
    ext X₀
    simp [mvfderiv_fun_mul hf (hσ.inner_bundle hτ),
      cov.isCovariantDerivativeOn.leibniz hσ hf, inner_add_left, inner_smul_left]
    ring
  add hσ hσ' := by
    ext X₀
    simp [mvfderiv_fun_add (hσ.inner_bundle hτ) (hσ'.inner_bundle hτ),
      cov.isCovariantDerivativeOn.add hσ hσ', inner_add_left]
    abel

theorem tensorial_derivMetricTensorAux₂ (σ : Π x, V x) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I F (derivMetricTensorAux I cov σ · x) x where
  smul hf hτ := by
    ext X₀
    simp [mvfderiv_fun_mul hf (hσ.inner_bundle hτ),
      cov.isCovariantDerivativeOn.leibniz hτ hf, inner_add_right, inner_smul_right]
    ring
  add hτ hτ' := by
    ext X₀
    simp [mvfderiv_fun_add (hσ.inner_bundle hτ) (hσ.inner_bundle hτ'),
      cov.isCovariantDerivativeOn.add hτ hτ', inner_add_right]
    abel

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- The tensor `(X, σ, τ) ↦ X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)` defining when a connection
`∇` on a Riemannian bundle `(M, V)` is compatible with the metric `g`. -/
public noncomputable def derivMetricTensor [FiniteDimensional ℝ F] (x : M) :
    V x →L[ℝ] V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  TensorialAt.mkHom₂ (derivMetricTensorAux I cov · · x) _
    (tensorial_derivMetricTensorAux₁ I cov) (tensorial_derivMetricTensorAux₂ I cov)

variable {X : Π x : M, TangentSpace I x}

variable {I} [ContMDiffVectorBundle 1 F V I] in
public theorem derivMetricTensor_apply [FiniteDimensional ℝ F] (x : M)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.derivMetricTensor x (σ x) (τ x) (X x) =
    d% ⟪σ, τ⟫ x (X x) - ⟪∇ X σ, τ⟫ x - ⟪σ, ∇ X τ⟫ x := by
  unfold derivMetricTensor
  rw [TensorialAt.mkHom₂_apply _ _ hσ hτ, derivMetricTensorAux_apply]

variable {I} [ContMDiffVectorBundle 1 F V I] in
public theorem derivMetricTensor_apply_eq_extend [FiniteDimensional ℝ F]
    (X₀ : TangentSpace I x) (σ₀ τ₀ : V x) :
    cov.derivMetricTensor x σ₀ τ₀ X₀ =
      d% ⟪(FiberBundle.extend F σ₀), (FiberBundle.extend F τ₀)⟫ x X₀
        - inner ℝ (cov (FiberBundle.extend F σ₀) x X₀) τ₀
        - inner ℝ σ₀ (cov (FiberBundle.extend F τ₀) x X₀) := by
  simp [derivMetricTensor, TensorialAt.mkHom₂_apply_eq_extend]

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- Predicate saying that a connection `∇` on a Riemannian bundle `(V, g)` is compatible with the
ambient metric, i.e. for all differentiable vector fields `X` on `M` and sections `σ` and `τ` of
`V`, we have `X ⟨σ, τ⟩ = ⟨∇_X σ, τ⟩ + ⟨σ, ∇_X τ⟩`. -/
public def IsMetricCompatible [FiniteDimensional ℝ F] : Prop := derivMetricTensor cov = 0

variable {I} [ContMDiffVectorBundle 1 F V I]

variable {cov} in
public lemma IsMetricCompatible.mvfderiv_inner_eq [FiniteDimensional ℝ F]
    (hcov : cov.IsMetricCompatible) {x : M} (X : Π x, TangentSpace I x) {σ τ : (x : M) → V x}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    d% ⟪σ, τ⟫ x (X x) = ⟪∇ X σ, τ⟫ x + ⟪σ, ∇ X τ⟫ x := by
  have H := congr($hcov x (σ x) (τ x) (X x))
  simp [derivMetricTensor_apply _ _ hσ hτ] at H
  linear_combination H

variable [IsManifold I 1 M]

public lemma isMetricCompatible_iff [FiniteDimensional ℝ F] :
    cov.IsMetricCompatible ↔ ∀ {x : M} {X : Π x, TangentSpace I x} {σ τ : (x : M) → V x},
      MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      d% ⟪σ, τ⟫ x (X x) = ⟪∇ X σ, τ⟫ x + ⟪σ, ∇ X τ⟫ x := by
  refine ⟨fun hcov x X σ τ hX ↦ hcov.mvfderiv_inner_eq X, fun h ↦ ?_⟩
  ext1 x
  apply VectorBundle.injective_eval_mdifferentiableAt_sec I F; ext1 σ; ext1 hσ
  apply VectorBundle.injective_eval_mdifferentiableAt_sec I F; ext1 τ; ext1 hτ
  apply VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I); ext X hX
  simp (disch := assumption) [derivMetricTensor_apply]
  linear_combination h hX hσ hτ

end CovariantDerivative
