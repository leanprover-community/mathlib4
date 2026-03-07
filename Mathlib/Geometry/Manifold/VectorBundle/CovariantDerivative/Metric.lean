/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.MfDerivSMul

/-! # Metric connections

This file defines connections on a Riemannian vector bundle which are compatible with the ambient
metric. A bundled connection `∇` on a Riemannian vector bundle `(V, g)` is compatible with the
metric `g` if and only if the differentiated metric tensor `∇ g` (defined by
`(X, Y, Z) ↦ ∇ₓ g(Y, Z) - g(∇ₓ Y, Z) - g(Y, ∇ₓ Z)`) vanishes on all differentiable vector fields `X`
and differentiable sections `Y`, `Z`.

## Main definitions and results

* `CovariantDerivative.compatibilityTensor`: the tensor
  `(X, Y, Z) ↦ ∇ₓ g(Y, Z) - g(∇ₓ Y, Z) - g(Y, ∇ₓ Z)` defining when a connection `∇` on a Riemannian
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

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Compatible connections: a connection on `V` is compatible with the metric on `M` iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all sufficiently nice vector fields `X` on `M` and
sections `Y`, `Z` of `V`. In our definition, we ask for this identity to at each `x : M`, whenever
`X`, `Y` and `Z` are differentiable at `x`.
The left hand side is the pushforward of the function `⟨Y, Z⟩` along the vector field `X`:
the left hand side at `x` is `df(X x)`, where `f := ⟨Y, Z⟩`. -/

variable {X X' X'' Y Y' Y'' Z Z' : Π x : M, V x}

/-- The scalar product of two vector fields -/
noncomputable abbrev product (X Y : Π x : M, V x) : M → ℝ :=
  fun x ↦ inner ℝ (X x) (Y x)

-- `product` is C^k if X and Y are: this is shown in `Riemannian.lean`

local notation "⟪" X ", " Y "⟫" => product X Y

-- Basic API for the product of two vector fields.
section product

omit [TopologicalSpace M] [IsManifold I 2 M]

lemma product_apply (x) : ⟪X, Y⟫ x = inner ℝ (X x) (Y x) := rfl

variable (X X' Y)

lemma product_swap : ⟪Y, X⟫ = ⟪X, Y⟫ := by
  ext x
  apply real_inner_comm

@[simp]
lemma product_zero_left : ⟪0, X⟫ = 0 := by
  ext x
  simp [product]

@[simp]
lemma product_zero_right : ⟪X, 0⟫ = 0 := by rw [product_swap, product_zero_left]

lemma product_add_left : ⟪X + X', Y⟫ = ⟪X, Y⟫ + ⟪X', Y⟫ := by
  ext x
  simp [product, InnerProductSpace.add_left]

@[simp]
lemma product_add_left_apply (x) : ⟪X + X', Y⟫ x = ⟪X, Y⟫ x + ⟪X', Y⟫ x := by
  simp [product, InnerProductSpace.add_left]

lemma product_add_right : ⟪X, Y + Y'⟫ = ⟪X, Y⟫ + ⟪X, Y'⟫ := by
  rw [product_swap, product_swap Y, product_swap Y', product_add_left]

@[simp]
lemma product_add_right_apply (x) : ⟪X, Y + Y'⟫ x = ⟪X, Y⟫ x + ⟪X, Y'⟫ x := by
  rw [product_swap, product_swap Y, product_swap Y', product_add_left_apply]

@[simp] lemma product_neg_left : ⟪-X, Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

@[simp] lemma product_neg_right : ⟪X, -Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

lemma product_sub_left : ⟪X - X', Y⟫ = ⟪X, Y⟫ - ⟪X', Y⟫ := by
  ext x
  simp [product, inner_sub_left]

lemma product_sub_right : ⟪X, Y - Y'⟫ = ⟪X, Y⟫ - ⟪X, Y'⟫ := by
  ext x
  simp [product, inner_sub_right]

lemma product_smul_left (f : M → ℝ) : product (f • X) Y = f • product X Y := by
  ext x
  simp [product, real_inner_smul_left]

@[simp]
lemma product_smul_const_left (a : ℝ) : product (a • X) Y = a • product X Y := by
  ext x
  simp [product, real_inner_smul_left]

lemma product_smul_right (f : M → ℝ) : product X (f • Y) = f • product X Y := by
  ext x
  simp [product, real_inner_smul_right]

@[simp]
lemma product_smul_const_right (a : ℝ) : product X (a • Y) = a • product X Y := by
  ext x
  simp [product, real_inner_smul_right]

end product

-- These lemmas are necessary as my Lie bracket identities (assuming minimal differentiability)
-- only hold point-wise. They abstract the expanding and unexpanding of `product`.
omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_left {x} (h : X x = X' x) : product X Y x = product X' Y x := by
  rw [product_apply, h, ← product_apply]

omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_left₂ {x} (h : X x = X' x + X'' x) :
    product X Y x = product X' Y x + product X'' Y x := by
  rw [product_apply, h, inner_add_left, ← product_apply]
omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_right {x} (h : Y x = Y' x) : product X Y x = product X Y' x := by
  rw [product_apply, h, ← product_apply]

omit [TopologicalSpace M] [IsManifold I 2 M] in
lemma product_congr_right₂ {x} (h : Y x = Y' x + Y'' x) :
    product X Y x = product X Y' x + product X Y'' x := by
  rw [product_apply, h, inner_add_right, ← product_apply]

/- TODO: writing `hY.inner_bundle hZ` or writing `by apply MDifferentiable.inner_bundle hY hZ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundle x
inferred
  fun b ↦ inst✝⁷
Diagnose and fix this, and then replace the below by `MDifferentiable(At).inner_bundle! -/

variable {F} [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {I} in
lemma MDifferentiable.inner_bundle' (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) : MDiff ⟪Y, Z⟫ :=
  MDifferentiable.inner_bundle hY hZ

variable {F} [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {I} in
lemma MDifferentiableAt.inner_bundle' {x} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt ⟪Y, Z⟫ x :=
  MDifferentiableAt.inner_bundle hY hZ

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `V`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I F V)

/-- Local notation for a connection. Caution: `∇ Y, X` corresponds to `∇ₓ Y` in textbooks -/
local notation "∇" Y "," X => fun (x:M) ↦ cov Y x (X x)

variable {F}

/-- The function defining the compatibility tensor for `∇` w.r.t. `g`:
prefer using `compatibilityTensor` instead -/
noncomputable def compatibilityTensorAux (Y Z : Π x : M, V x) :
    Π (x : M), TangentSpace I x →L[ℝ] ℝ := fun x ↦
  letI b : TangentSpace I x →L[ℝ] ℝ := mfderiv% ⟪Y, Z⟫ x
  b - ((innerSL ℝ (Z x)) ∘L (cov Y x)) - ((innerSL ℝ (Y x)) ∘L (cov Z x))

lemma compatibilityTensorAux_apply (Y Z : Π x : M, V x)
    {x : M} (X₀ : TangentSpace I x) :
    compatibilityTensorAux I cov Y Z x X₀ =
      NormedSpace.fromTangentSpace _ (mfderiv% ⟪Y, Z⟫ x X₀)
      - innerSL ℝ (Z x) (cov Y x X₀) - innerSL ℝ (Y x) (cov Z x X₀) := by
  unfold compatibilityTensorAux
  simp
  congr 1

variable [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V] {x : M}

variable {I} in
private lemma aux1 {f : M → ℝ} {σ τ : (x : M) → V x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensorAux I cov (f • σ) τ x = f x • compatibilityTensorAux I cov σ τ x := by
  ext X₀
  rw [compatibilityTensorAux_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    compatibilityTensorAux_apply]
  rw [product_smul_left, cov.isCovariantDerivativeOn.leibniz hσ hf]
  simp only [Pi.smul_apply', ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, coe_innerSL_apply, map_smul]
  erw [mfderiv_smul (hσ.inner_bundle' hτ) hf] -- identifying different tangent spaces
  rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm (σ x) (τ x)]
  simp only [← smul_eq_mul]
  module

variable {I} in
private lemma aux2 (σ σ' τ : (x : M) → V x)
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensorAux I cov (σ + σ') τ x =
      compatibilityTensorAux I cov σ τ x + compatibilityTensorAux I cov σ' τ x := by
  simp only [compatibilityTensorAux]
  ext X
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp', coe_innerSL_apply,
    Pi.sub_apply, comp_apply, ContinuousLinearMap.add_apply]
  rw [product_add_left,
    mfderiv_add (hσ.inner_bundle' hτ) (hσ'.inner_bundle' hτ),
    cov.isCovariantDerivativeOn.add hσ hσ',
    ContinuousLinearMap.comp_add]
  erw [ContinuousLinearMap.coe_sub']
  rw [Pi.sub_apply]
  erw [ContinuousLinearMap.add_apply, Pi.add_apply, inner_add_left]
  -- set A := mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ⟫ x
  -- set A' := mfderiv I 𝓘(ℝ, ℝ) ⟪σ', τ⟫ x
  -- set B := ((innerSL ℝ) (τ x)).comp (cov σ x)
  -- set B' := ((innerSL ℝ) (τ x)).comp (cov σ' x)
  -- set C := inner ℝ (σ x) ((cov τ x) X)
  -- set C' := inner ℝ (σ' x) ((cov τ x) X)
  erw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply]
  -- bug: abel fails, but module works
  -- hypothesis: B, B', C, C' are in ℝ, while A and A' are in the tangent space at ℝ instead
  module

variable {I} in
private lemma aux3 {f : M → ℝ} {σ τ : (x : M) → V x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    compatibilityTensorAux I cov σ (f • τ) x = f x • compatibilityTensorAux I cov σ τ x := by
  unfold compatibilityTensorAux
  rw [product_smul_right, cov.isCovariantDerivativeOn.leibniz hτ hf]
  ext X
  simp only [smul_eq_mul, Pi.smul_apply', map_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
    ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', coe_innerSL_apply, Pi.smul_apply,
    comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.toSpanSingleton_apply]
  erw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  --set A := inner ℝ (σ x) ((cov τ x) X)
  conv =>
    enter [1, 1, 2]
    erw [ContinuousLinearMap.smul_apply]
  conv =>
    enter [1, 1, 2, 2]
    erw [ContinuousLinearMap.comp_apply]
  dsimp
  --set B := inner ℝ (τ x) ((cov σ x) X)
  erw [mfderiv_smul (hσ.inner_bundle' hτ) hf]
  --set C := (mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ⟫ x) X
  --set D := (mfderiv I 𝓘(ℝ, ℝ) f x) X
  simp only [smul_eq_mul, fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, inner_smul_right]
  -- would be nice to finish by a tactic now!
  erw [mul_add, mul_add]
  rw [Pi.mul_apply, mul_neg, mul_neg,
    ← sub_eq_add_neg, ← sub_eq_add_neg, sub_add_eq_sub_sub]
  match_scalars <;> all_goals simp

variable {I} in
private lemma aux4 (σ τ τ' : (x : M) → V x)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x) :
    compatibilityTensorAux I cov σ (τ + τ') x =
      compatibilityTensorAux I cov σ τ x + compatibilityTensorAux I cov σ τ' x := by
  ext X₀
  rw [compatibilityTensorAux_apply]; dsimp
  rw [compatibilityTensorAux_apply, compatibilityTensorAux_apply]; dsimp
  rw [product_add_right, mfderiv_add (hσ.inner_bundle' hτ) (hσ.inner_bundle' hτ'),
    cov.isCovariantDerivativeOn.add hτ hτ']
  simp only [Pi.add_apply, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    fromTangentSpace, -- this line is slightly fishy
    ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  erw [ContinuousLinearMap.add_apply]
  module

theorem compatibilityTensorAux_tensorial₁ (τ : Π x, V x) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I F (compatibilityTensorAux I cov · τ x) x where
  smul hf hσ := aux1 cov hf hσ hτ
  add hσ hσ' := aux2 cov _ _ _ hσ hσ' hτ

theorem compatibilityTensorAux_tensorial₂ (σ : Π x, V x) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I F (compatibilityTensorAux I cov σ · x) x where
  smul hf hτ := aux3 cov hf hσ hτ
  add hτ hτ' := aux4 cov _ _ _ hσ hτ hτ'

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- The tensor `(X, Y, Z) ↦ ∇ₓ g(Y, Z) - g(∇ₓ Y, Z) - g(Y, ∇ₓ Z)` defining when a connection
`∇` on a Riemannian bundle `(M, V)` is compatible with the metric `g`. -/
@[no_expose] noncomputable def compatibilityTensor [FiniteDimensional ℝ F] (x : M) :
    V x →L[ℝ] V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  TensorialAt.mkHom₂ (compatibilityTensorAux I cov · · x) _
    (compatibilityTensorAux_tensorial₁ I cov) (compatibilityTensorAux_tensorial₂ I cov)

variable {X : Π x : M, TangentSpace I x}

variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem compatibilityTensor_apply [FiniteDimensional ℝ F] (x : M)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    compatibilityTensor cov x (Y x) (Z x) (X x) =
    fromTangentSpace _ (mfderiv% ⟪Y, Z⟫ x (X x)) - ⟪∇ Y, X, Z⟫ x - ⟪Y, ∇ Z, X⟫ x := by
  unfold compatibilityTensor
  rw [TensorialAt.mkHom₂_apply _ _ hY hZ]
  --rw [compatibilityTensorAux_apply]
  simp only [compatibilityTensorAux, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp',
    coe_innerSL_apply, Pi.sub_apply, comp_apply]
  conv =>
    enter [1, 1]
    erw [ContinuousLinearMap.sub_apply]
  conv =>
    enter [1, 1, 2]
    erw [ContinuousLinearMap.comp_apply]
  simp [product, real_inner_comm, fromTangentSpace]

open FiberBundle in
variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem compatibilityTensor_apply_eq_extend [FiniteDimensional ℝ F] (X₀ : TangentSpace I x)
    (Y₀ Z₀ : V x) :
    compatibilityTensor cov x Y₀ Z₀ X₀ =
      fromTangentSpace _ (mfderiv% ⟪(extend F Y₀), (extend F Z₀)⟫ x X₀)
        - ⟪∇ extend F Y₀, (extend E X₀), extend F Z₀⟫ x
        - ⟪extend F Y₀, ∇ extend F Z₀, (extend E X₀)⟫ x := by
  simpa [extend_apply_self] using compatibilityTensor_apply cov x
    (X := extend E X₀) (mdifferentiableAt_extend I F Y₀) (mdifferentiableAt_extend I F Z₀)

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- Predicate saying for a connection `∇` on a Riemannian bundle `(V, g)` to be compatible with
the ambient metric, i.e. for all differentiable vector fields `X` on `M` and sections `Y` and `Z`
of `V`, we have
`X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩`. -/
def IsCompatible [FiniteDimensional ℝ F] : Prop := compatibilityTensor cov = 0

-- Auxiliary computation for `IsCompatible_apply`.
-- TODO: inlining this lemma does not work
private lemma isCompatible_apply_aux {A B C : ℝ} (h : A - B - C = 0) : A = B + C := by grind

variable {I} [ContMDiffVectorBundle 1 F V I] in
-- TODO: give a better name; maybe inline?
-- variable {I} in
lemma isCompatible_apply [FiniteDimensional ℝ F] (hcov : cov.IsCompatible)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mfderiv% ⟪Y, Z⟫ x (X x) = ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ Z, X⟫ x := by
  rw [IsCompatible] at hcov
  have : compatibilityTensor cov x (Y x) (Z x) (X x) = 0 := by simp [hcov]
  rw [compatibilityTensor_apply cov x hY hZ] at this
  change (fromTangentSpace _ ((mfderiv I 𝓘(ℝ, ℝ) ⟪Y, Z⟫ x) (X x))) = _
  exact isCompatible_apply_aux this

open FiberBundle in
variable {I} [ContMDiffVectorBundle 1 F V I] in
lemma isCompatible_iff [FiniteDimensional ℝ F] :
    cov.IsCompatible ↔ ∀ {x : M} {X : Π x, TangentSpace I x} {Y Z : (x : M) → V x}
      (_hX : MDiffAt (T% X) x) (_hY : MDiffAt (T% Y) x) (_hZ : MDiffAt (T% Z) x),
      mfderiv% ⟪Y, Z⟫ x (X x) = ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ Z, X⟫ x := by
  refine ⟨fun hcov x X Y Z hX hY hZ ↦ cov.isCompatible_apply hcov hY hZ, fun h ↦ ?_⟩
  unfold IsCompatible
  ext x Y₀ Z₀ X₀
  rw [compatibilityTensor_apply_eq_extend, sub_sub, sub_eq_iff_eq_add']
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, add_zero]
  have h' := h (mdifferentiableAt_extend I E X₀) (mdifferentiableAt_extend I F Y₀)
    (mdifferentiableAt_extend I F Z₀)
  simpa [fromTangentSpace, extend_apply_self] using h'

end CovariantDerivative
