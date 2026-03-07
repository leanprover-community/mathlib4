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
`(X, σ, τ) ↦ ∇ₓ g(σ, τ) - g(∇ₓ σ, τ) - g(σ, ∇ₓ τ)`) vanishes on all differentiable vector fields `X`
and differentiable sections `σ`, `τ`.

## Main definitions and results

* `CovariantDerivative.compatibilityTensor`: the tensor
  `(X, σ, τ) ↦ ∇ₓ g(σ, τ) - g(∇ₓ σ, τ) - g(σ, ∇ₓ τ)` defining when a connection `∇` on a Riemannian
  vector bundle `(V, g)` is compatible with the metric `g`.
* `CovariantDerivative.compatibilityTensor_apply` and
  `CovariantDerivative.compatibilityTensor_apply` give formulas for applying the compatibility
  tensor at `x` to vector fields and sections which are differentiable at `x`,
  resp. to extensions of tangent vectors and sections at `x` to differentiable vector fields and
  sections near `x`.
* `CovariantDerivative.IsCompatible`: predicate for a connection to be metric, namely that
  `∇` is metric iff its `compatibilityTensor` vanishes

## TODO

* when mathlib has a notion of parallel transport, prove the equivalence of
  `CovariantDerivative.IsCompatible` with the characterisation that parallel transport be an
  isometry.

-/

open Bundle Function NormedSpace
open scoped Manifold ContDiff

@[expose] public section

-- TODO: revisit and fix this once the dust has settled
set_option backward.isDefEq.respectTransparency false

variable
  -- Let `M` be a `C^k` real manifold modeled on `(E, H)`
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  -- Let `V` be a bundle over `M`, endowed with a Riemannian metric.
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [RiemannianBundle V]

/-! Compatible connections: a connection on `V` is compatible with the metric on `V` iff
`∇ X ⟨σ, τ⟩ = ⟨∇ X σ, τ⟩ + ⟨σ, ∇ X τ⟩` holds for all sufficiently nice vector fields `X` on `M` and
sections `σ`, `τ` of `V`. In our definition, we ask for this identity to at each `x : M`, whenever
`X`, `σ` and `τ` are differentiable at `x`.
The left hand side is the pushforward of the function `⟨σ, τ⟩` along the vector field `X`:
the left hand side at `x` is `df(X x)`, where `f := ⟨σ, τ⟩`. -/

variable {σ σ' σ'' τ τ' τ'' : Π x : M, V x}

/-- The scalar product of two sections. -/
noncomputable abbrev product (σ τ : Π x : M, V x) : M → ℝ :=
  fun x ↦ inner ℝ (σ x) (τ x)

-- `product` is C^k if σ and τ are: this is shown in `Riemannian.lean`

local notation "⟪" σ ", " τ "⟫" => product σ τ

-- Basic API for the product of two sections.
section product

omit [TopologicalSpace M] [IsManifold I 2 M]

lemma product_apply (x) : ⟪σ, τ⟫ x = inner ℝ (σ x) (τ x) := rfl

variable (σ σ' τ)

lemma product_swap : ⟪τ, σ⟫ = ⟪σ, τ⟫ := by
  ext x
  apply real_inner_comm

@[simp]
lemma product_zero_left : ⟪0, σ⟫ = 0 := by
  ext x
  simp [product]

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
omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_left {x} (h : σ x = σ' x) : product σ τ x = product σ' τ x := by
  rw [product_apply, h, ← product_apply]

omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_left₂ {x} (h : σ x = σ' x + σ'' x) :
    product σ τ x = product σ' τ x + product σ'' τ x := by
  rw [product_apply, h, inner_add_left, ← product_apply]
omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_right {x} (h : τ x = τ' x) : product σ τ x = product σ τ' x := by
  rw [product_apply, h, ← product_apply]

omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_right₂ {x} (h : τ x = τ' x + τ'' x) :
    product σ τ x = product σ τ' x + product σ τ'' x := by
  rw [product_apply, h, inner_add_right, ← product_apply]

/- TODO: writing `hσ.inner_bundle hτ` or writing `by apply MDifferentiable.inner_bundle hσ hτ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundle x
inferred
  fun b ↦ inst✝⁷
Diagnose and fix this, and then replace the below by `MDifferentiable(At).inner_bundle! -/

variable {F} [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {I} in
lemma MDifferentiable.inner_bundle' (hσ : MDiff (T% σ)) (hτ : MDiff (T% τ)) : MDiff ⟪σ, τ⟫ :=
  MDifferentiable.inner_bundle hσ hτ

variable {F} [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {I} in
lemma MDifferentiableAt.inner_bundle' {x} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt ⟪σ, τ⟫ x :=
  MDifferentiableAt.inner_bundle hσ hτ

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `V`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I F V)

/-- Local notation for a connection. Caution: `∇ σ, X` corresponds to `∇ₓ σ` in textbooks -/
local notation "∇" σ "," X => fun (x:M) ↦ cov σ x (X x)

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
      - innerSL ℝ (τ x) (cov σ x X₀) - innerSL ℝ (σ x) (cov τ x X₀) :=
  rfl

variable [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {x : M}

variable {I} in
private lemma aux1 {f : M → ℝ} {σ τ : (x : M) → V x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensorAux I cov (f • σ) τ x = f x • compatibilityTensorAux I cov σ τ x := by
  ext X₀
  rw [compatibilityTensorAux_apply, product_smul_left,
    fromTangentSpace_mfderiv_smul_apply hf (hσ.inner_bundle' hτ)]
  simp [compatibilityTensorAux, cov.isCovariantDerivativeOn.leibniz hσ hf, inner_add_right,
    inner_smul_right, real_inner_comm]
  ring

variable {I} in
private lemma aux2 (σ σ' τ : (x : M) → V x)
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensorAux I cov (σ + σ') τ x =
      compatibilityTensorAux I cov σ τ x + compatibilityTensorAux I cov σ' τ x := by
  ext X₀
  rw [compatibilityTensorAux_apply, product_add_left,
    fromTangentSpace_mfderiv_add_apply (hσ.inner_bundle' hτ) (hσ'.inner_bundle' hτ)]
  simp [compatibilityTensorAux_apply, cov.isCovariantDerivativeOn.add hσ hσ', inner_add_right]
  abel

variable {I} in
private lemma aux3 {f : M → ℝ} {σ τ : (x : M) → V x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensorAux I cov σ (f • τ) x = f x • compatibilityTensorAux I cov σ τ x := by
  ext X₀
  rw [compatibilityTensorAux_apply, product_smul_right,
    fromTangentSpace_mfderiv_smul_apply hf (hσ.inner_bundle' hτ)]
  simp [compatibilityTensorAux, cov.isCovariantDerivativeOn.leibniz hτ hf, inner_add_right,
    inner_smul_right, real_inner_comm]
  ring

variable {I} in
private lemma aux4 (σ τ τ' : (x : M) → V x)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x) :
    compatibilityTensorAux I cov σ (τ + τ') x =
      compatibilityTensorAux I cov σ τ x + compatibilityTensorAux I cov σ τ' x := by
  ext X₀
  rw [compatibilityTensorAux_apply, product_add_right,
    fromTangentSpace_mfderiv_add_apply (hσ.inner_bundle' hτ) (hσ.inner_bundle' hτ')]
  simp [compatibilityTensorAux_apply, cov.isCovariantDerivativeOn.add hτ hτ', inner_add_right]
  abel

theorem compatibilityTensorAux_tensorial₁ (τ : Π x, V x) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I F (compatibilityTensorAux I cov · τ x) x where
  smul hf hσ := aux1 cov hf hσ hτ
  add hσ hσ' := aux2 cov _ _ _ hσ hσ' hτ

theorem compatibilityTensorAux_tensorial₂ (σ : Π x, V x) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I F (compatibilityTensorAux I cov σ · x) x where
  smul hf hτ := aux3 cov hf hσ hτ
  add hτ hτ' := aux4 cov _ _ _ hσ hτ hτ'

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- The tensor `(X, σ, τ) ↦ ∇ₓ g(σ, τ) - g(∇ₓ σ, τ) - g(σ, ∇ₓ τ)` defining when a connection
`∇` on a Riemannian bundle `(M, V)` is compatible with the metric `g`. -/
@[no_expose] noncomputable def compatibilityTensor [FiniteDimensional ℝ F] (x : M) :
    V x →L[ℝ] V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  TensorialAt.mkHom₂ (compatibilityTensorAux I cov · · x) _
    (compatibilityTensorAux_tensorial₁ I cov) (compatibilityTensorAux_tensorial₂ I cov)

variable {X : Π x : M, TangentSpace I x}

variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem compatibilityTensor_apply [FiniteDimensional ℝ F] (x : M)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensor cov x (σ x) (τ x) (X x) =
    fromTangentSpace _ (mfderiv% ⟪σ, τ⟫ x (X x)) - ⟪∇ σ, X, τ⟫ x - ⟪σ, ∇ τ, X⟫ x := by
  unfold compatibilityTensor
  rw [TensorialAt.mkHom₂_apply _ _ hσ hτ]
  --rw [compatibilityTensorAux]
  simp only [compatibilityTensorAux, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp',
    coe_innerSL_apply, Pi.sub_apply, comp_apply]
  conv =>
    enter [1, 1]
    erw [ContinuousLinearMap.sub_apply]
  conv =>
    enter [1, 1, 2]
    erw [ContinuousLinearMap.comp_apply]
  simp [product, real_inner_comm, fromTangentSpace]

variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem compatibilityTensor_apply_eq_extend [FiniteDimensional ℝ F] (X₀ : TangentSpace I x)
    (σ₀ τ₀ : V x) :
    compatibilityTensor cov x σ₀ τ₀ X₀ =
      fromTangentSpace _ (mfderiv% ⟪(FiberBundle.extend F σ₀), (FiberBundle.extend F τ₀)⟫ x X₀)
        - ⟪∇ FiberBundle.extend F σ₀, (FiberBundle.extend E X₀), FiberBundle.extend F τ₀⟫ x
        - ⟪FiberBundle.extend F σ₀, ∇ FiberBundle.extend F τ₀, (FiberBundle.extend E X₀)⟫ x := by
  simpa [extend_apply_self] using compatibilityTensor_apply cov x (X := FiberBundle.extend E X₀)
    (FiberBundle.mdifferentiableAt_extend I F σ₀) (FiberBundle.mdifferentiableAt_extend I F τ₀)

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- Predicate saying that a connection `∇` on a Riemannian bundle `(V, g)` is compatible with the
ambient metric, i.e. for all differentiable vector fields `X` on `M` and sections `σ` and `τ` of
`V`, we have `X ⟨σ, τ⟩ = ⟨∇ X σ, τ⟩ + ⟨σ, ∇ X τ⟩`. -/
def IsCompatible [FiniteDimensional ℝ F] : Prop := compatibilityTensor cov = 0

-- Auxiliary computation for `IsCompatible_apply`.
-- TODO: inlining this lemma does not work
private lemma isCompatible_apply_aux {A B C : ℝ} (h : A - B - C = 0) : A = B + C := by grind

variable {I} [ContMDiffVectorBundle 1 F V I] in
-- TODO: give a better name; maybe inline?
-- variable {I} in
lemma isCompatible_apply [FiniteDimensional ℝ F] (hcov : cov.IsCompatible)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    mfderiv% ⟪σ, τ⟫ x (X x) = ⟪∇ σ, X, τ⟫ x + ⟪σ, ∇ τ, X⟫ x := by
  rw [IsCompatible] at hcov
  have : compatibilityTensor cov x (σ x) (τ x) (X x) = 0 := by simp [hcov]
  rw [compatibilityTensor_apply cov x hσ hτ] at this
  change (fromTangentSpace _ ((mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ⟫ x) (X x))) = _
  exact isCompatible_apply_aux this

open FiberBundle in
variable {I} [ContMDiffVectorBundle 1 F V I] in
lemma isCompatible_iff [FiniteDimensional ℝ F] :
    cov.IsCompatible ↔ ∀ {x : M} {X : Π x, TangentSpace I x} {σ τ : (x : M) → V x}
      (_hX : MDiffAt (T% X) x) (_hσ : MDiffAt (T% σ) x) (_hτ : MDiffAt (T% τ) x),
      mfderiv% ⟪σ, τ⟫ x (X x) = ⟪∇ σ, X, τ⟫ x + ⟪σ, ∇ τ, X⟫ x := by
  refine ⟨fun hcov x X σ τ hX hσ hτ ↦ cov.isCompatible_apply hcov hσ hτ, fun h ↦ ?_⟩
  unfold IsCompatible
  ext x σ₀ τ₀ X₀
  rw [compatibilityTensor_apply_eq_extend, sub_sub, sub_eq_iff_eq_add']
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, add_zero]
  have h' := h (FiberBundle.mdifferentiableAt_extend I E X₀)
    (FiberBundle.mdifferentiableAt_extend I F σ₀) (FiberBundle.mdifferentiableAt_extend I F τ₀)
  simpa [fromTangentSpace, extend_apply_self] using h'

end CovariantDerivative
