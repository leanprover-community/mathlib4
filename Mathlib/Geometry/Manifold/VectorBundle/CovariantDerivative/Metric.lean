/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Metric connections

This file defines connections on a Riemannian vector bundle which are compatible with the ambient
metric. A bundled connection `∇` on a Riemannian vector bundle `(V, g)` is compatible with the
metric `g` if and only if the differentiated metric tensor `∇ g` (defined by
`(X, σ, τ) ↦ ∇_X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)`) vanishes on all differentiable vector fields
`X` and differentiable sections `σ`, `τ`.

## Main definitions and results

* `CovariantDerivative.compatibilityTensor`: the tensor
  `(X, σ, τ) ↦ X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)` defining when a connection `∇` on a Riemannian
  vector bundle `(V, g)` is compatible with the metric `g`.
* `CovariantDerivative.compatibilityTensor_apply` and
  `CovariantDerivative.compatibilityTensor_apply` give formulas for applying the compatibility
  tensor at `x` to vector fields and sections which are differentiable at `x`,
  resp. to extensions of tangent vectors and sections at `x` to differentiable vector fields and
  sections near `x`.
* `CovariantDerivative.IsCompatible`: predicate for a connection to be metric, namely that
  `∇` is metric iff its `compatibilityTensor` vanishes

## TODO

* When Mathlib has a notion of parallel transport, prove the equivalence of
 `CovariantDerivative.IsCompatible` with the characterisation that parallel transport be an
  isometry.

* Given connections on bundles `V` and `W`, there is an induced connnection on the bundle Hom(V, W).
  When this induced connection has been defined in Mathlib, rephrase the definition of
  `CovariantDerivative.compatibilityTensor`, to be simply the covariant derivative of the metric
  tensor (considered as a section of Hom(V, Hom(V, ℝ))).

-/
open Bundle NormedSpace
open scoped Manifold ContDiff

@[expose] public section

-- TODO: revisit and fix this once the dust has settled
set_option backward.isDefEq.respectTransparency false

variable
  -- Let `M` be a `C^k` real manifold modeled on `(E, H)`
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Let `V` be a bundle over `M`, endowed with a Riemannian metric.
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [RiemannianBundle V]

/-! # Compatible connections

A connection on `V` is compatible with the metric on `V` iff `X ⟨σ, τ⟩ = ⟨∇_X σ, τ⟩ + ⟨σ, ∇_X τ⟩`
holds for all sufficiently nice vector fields `X` on `M` and sections `σ`, `τ` of `V`.
The left hand side is the pushforward of the function `⟨σ, τ⟩` along the vector field `X`:
the left hand side at `x` is `df(X x)`, where `f := ⟨σ, τ⟩` (ie. `X` is seen a derivation on
the algebra of function on the base manifold acting on the function `⟨σ, τ⟩`).
In our definition, we ask for this identity to at each `x : M`, whenever `X`, `σ` and `τ` are
differentiable at `x`.
-/

variable {σ σ' σ'' τ τ' τ'' : Π x : M, V x}

-- set_option trace.profiler true
-- set_option profiler.threshold 500

/-- The scalar product of two sections. -/
noncomputable abbrev product (σ τ : Π x : M, V x) : M → ℝ :=
  fun x ↦ inner ℝ (σ x) (τ x)

-- `product` is C^k if σ and τ are: this is shown in `Riemannian.lean`

local notation "⟪" σ ", " τ "⟫" => product σ τ

-- Basic API for the product of two sections.
section product

omit [TopologicalSpace M]

lemma product_apply (x) : ⟪σ, τ⟫ x = inner ℝ (σ x) (τ x) := rfl

variable (σ σ' τ)

lemma product_swap : ⟪τ, σ⟫ = ⟪σ, τ⟫ := by
  ext x
  apply real_inner_comm

@[simp]
lemma product_zero_left : ⟪0, σ⟫ = 0 := by
  ext x
  simp only [product, Pi.zero_apply, inner_zero_left]

@[simp]
lemma product_zero_right : ⟪σ, 0⟫ = 0 := by rw [product_swap, product_zero_left]

lemma product_add_left : ⟪σ + σ', τ⟫ = ⟪σ, τ⟫ + ⟪σ', τ⟫ := by
  ext x
  simp [product, InnerProductSpace.add_left]

@[simp]
lemma product_add_left_apply (x) : ⟪σ + σ', τ⟫ x = ⟪σ, τ⟫ x + ⟪σ', τ⟫ x := by
  simp [product, InnerProductSpace.add_left]

lemma product_add_right : ⟪σ, τ + τ'⟫ = ⟪σ, τ⟫ + ⟪σ, τ'⟫ := by
  rw [product_swap, product_swap τ, product_swap τ', product_add_left]

@[simp]
lemma product_add_right_apply (x) : ⟪σ, τ + τ'⟫ x = ⟪σ, τ⟫ x + ⟪σ, τ'⟫ x := by
  rw [product_swap, product_swap τ, product_swap τ', product_add_left_apply]

@[simp] lemma product_neg_left : ⟪-σ, τ⟫ = -⟪σ, τ⟫ := by ext x; simp [product]

@[simp] lemma product_neg_right : ⟪σ, -τ⟫ = -⟪σ, τ⟫ := by ext x; simp [product]

lemma product_sub_left : ⟪σ - σ', τ⟫ = ⟪σ, τ⟫ - ⟪σ', τ⟫ := by
  ext x
  simp [product, inner_sub_left]

lemma product_sub_right : ⟪σ, τ - τ'⟫ = ⟪σ, τ⟫ - ⟪σ, τ'⟫ := by
  ext x
  simp [product, inner_sub_right]

lemma product_smul_left (f : M → ℝ) : product (f • σ) τ = f • product σ τ := by
  ext x
  simp [product, real_inner_smul_left]

@[simp]
lemma product_smul_const_left (a : ℝ) : product (a • σ) τ = a • product σ τ := by
  ext x
  simp [product, real_inner_smul_left]

lemma product_smul_right (f : M → ℝ) : product σ (f • τ) = f • product σ τ := by
  ext x
  simp [product, real_inner_smul_right]

@[simp]
lemma product_smul_const_right (a : ℝ) : product σ (a • τ) = a • product σ τ := by
  ext x
  simp [product, real_inner_smul_right]

end product

-- These lemmas are necessary as my Lie bracket identities (assuming minimal differentiability)
-- only hold point-wise. They abstract the expanding and unexpanding of `product`.
omit [TopologicalSpace M] in
lemma product_congr_left {x} (h : σ x = σ' x) : product σ τ x = product σ' τ x := by
  rw [product_apply, h, ← product_apply]

omit [TopologicalSpace M] in
lemma product_congr_left₂ {x} (h : σ x = σ' x + σ'' x) :
    product σ τ x = product σ' τ x + product σ'' τ x := by
  rw [product_apply, h, inner_add_left, ← product_apply]
omit [TopologicalSpace M] in
lemma product_congr_right {x} (h : τ x = τ' x) : product σ τ x = product σ τ' x := by
  rw [product_apply, h, ← product_apply]

omit [TopologicalSpace M] in
lemma product_congr_right₂ {x} (h : τ x = τ' x + τ'' x) :
    product σ τ x = product σ τ' x + product σ τ'' x := by
  rw [product_apply, h, inner_add_right, ← product_apply]

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `V`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I F V)


/-- Local notation for a covariant derivative on a vector bundle acting on a vector field and a
section. -/
local syntax "∇" term:arg term : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))

variable {F}

/-- The function defining the compatibility tensor for `∇` w.r.t. `g`:
prefer using `compatibilityTensor` instead -/
noncomputable def compatibilityTensorAux (σ τ : Π x : M, V x) :
    Π (x : M), TangentSpace I x →L[ℝ] ℝ := fun x ↦
  (NormedSpace.fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% ⟪σ, τ⟫ x
  - ((innerSL ℝ (τ x)) ∘L (cov σ x)) - ((innerSL ℝ (σ x)) ∘L (cov τ x))

lemma compatibilityTensorAux_apply (σ τ : Π x : M, V x)
    {x : M} (X₀ : TangentSpace I x) :
    compatibilityTensorAux I cov σ τ x X₀ =
      NormedSpace.fromTangentSpace _ (mfderiv% ⟪σ, τ⟫ x X₀)
      - inner ℝ (cov σ x X₀) (τ x) - inner ℝ (σ x) (cov τ x X₀) := by
  rw [real_inner_comm]
  rfl

variable [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {x : M}

theorem compatibilityTensorAux_tensorial₁ (τ : Π x, V x) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I F (compatibilityTensorAux I cov · τ x) x where
  smul hf hσ := by
    ext X₀
    rw [compatibilityTensorAux_apply, product_smul_left,
      fromTangentSpace_mfderiv_smul_apply hf (hσ.inner_bundle hτ)]
    simp [compatibilityTensorAux_apply, cov.isCovariantDerivativeOn.leibniz hσ hf, inner_add_left,
      inner_smul_left]
    ring
  add hσ hσ' := by
    ext X₀
    rw [compatibilityTensorAux_apply, product_add_left,
      fromTangentSpace_mfderiv_add_apply (hσ.inner_bundle hτ) (hσ'.inner_bundle hτ)]
    simp [compatibilityTensorAux_apply, cov.isCovariantDerivativeOn.add hσ hσ', inner_add_left]
    abel

theorem compatibilityTensorAux_tensorial₂ (σ : Π x, V x) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I F (compatibilityTensorAux I cov σ · x) x where
  smul hf hτ := by
    ext X₀
    rw [compatibilityTensorAux_apply, product_smul_right,
      fromTangentSpace_mfderiv_smul_apply hf (hσ.inner_bundle hτ)]
    simp [compatibilityTensorAux_apply, cov.isCovariantDerivativeOn.leibniz hτ hf, inner_add_right,
      inner_smul_right]
    ring
  add hτ hτ' := by
    ext X₀
    rw [compatibilityTensorAux_apply, product_add_right,
      fromTangentSpace_mfderiv_add_apply (hσ.inner_bundle hτ) (hσ.inner_bundle hτ')]
    simp [compatibilityTensorAux_apply, cov.isCovariantDerivativeOn.add hτ hτ', inner_add_right]
    abel

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- The tensor `(X, σ, τ) ↦ X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)` defining when a connection
`∇` on a Riemannian bundle `(M, V)` is compatible with the metric `g`. -/
@[no_expose] noncomputable def compatibilityTensor [FiniteDimensional ℝ F] (x : M) :
    V x →L[ℝ] V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  TensorialAt.mkHom₂ (compatibilityTensorAux I cov · · x) _
    (compatibilityTensorAux_tensorial₁ I cov) (compatibilityTensorAux_tensorial₂ I cov)

variable {X : Π x : M, TangentSpace I x}

variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem compatibilityTensor_apply [FiniteDimensional ℝ F] (x : M)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.compatibilityTensor x (σ x) (τ x) (X x) =
    fromTangentSpace _ (mfderiv% ⟪σ, τ⟫ x (X x)) - ⟪∇ X σ, τ⟫ x - ⟪σ, ∇ X τ⟫ x := by
  unfold compatibilityTensor
  rw [TensorialAt.mkHom₂_apply _ _ hσ hτ, compatibilityTensorAux_apply]

open FiberBundle in
variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem compatibilityTensor_apply_eq_extend [FiniteDimensional ℝ F] (X₀ : TangentSpace I x)
    (σ₀ τ₀ : V x) :
    cov.compatibilityTensor x σ₀ τ₀ X₀ =
      fromTangentSpace _ (mfderiv% ⟪(extend F σ₀), (extend F τ₀)⟫ x X₀)
        - inner ℝ (cov (extend F σ₀) x X₀) τ₀
        - inner ℝ σ₀ (cov (extend F τ₀) x X₀) := by
  simp [compatibilityTensor, TensorialAt.mkHom₂_apply_eq_extend, compatibilityTensorAux_apply]

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- Predicate saying that a connection `∇` on a Riemannian bundle `(V, g)` is compatible with the
ambient metric, i.e. for all differentiable vector fields `X` on `M` and sections `σ` and `τ` of
`V`, we have `X ⟨σ, τ⟩ = ⟨∇_X σ, τ⟩ + ⟨σ, ∇_X τ⟩`. -/
def IsCompatible [FiniteDimensional ℝ F] : Prop := compatibilityTensor cov = 0

variable {I} [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

open FiberBundle in
lemma isCompatible_iff [FiniteDimensional ℝ F] :
    cov.IsCompatible ↔ ∀ {x : M} {X : Π x, TangentSpace I x} {σ τ : (x : M) → V x},
      MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      fromTangentSpace _ (mfderiv% ⟪σ, τ⟫ x (X x)) = ⟪∇ X σ, τ⟫ x + ⟪σ, ∇ X τ⟫ x := by
  refine ⟨fun hcov x X σ τ hX hσ hτ ↦ ?_, fun h ↦ ?_⟩
  · have H := congr($hcov x (σ x) (τ x) (X x))
    simp [compatibilityTensor_apply _ _ hσ hτ] at H
    linear_combination H
  ext x σ₀ τ₀ X₀
  rw [compatibilityTensor_apply_eq_extend]
  have h' := h (mdifferentiableAt_extend I E X₀) (mdifferentiableAt_extend I F σ₀)
    (mdifferentiableAt_extend I F τ₀)
  simp [product] at h' ⊢
  linear_combination h'

end CovariantDerivative
