/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! # Metric connections

This file defines connections on a Riemannian manifold which are compatible with the ambient metric.

TODO extend this doc-string!


TODO: more generally, define a notion of metric connections (e.g., those whose parallel transport
is an isometry) and prove the Levi-Civita connection is a metric connection

-/

open Bundle Filter Function Module NormedSpace Topology

open scoped Bundle Manifold ContDiff

@[expose] public section -- TODO: think if we want to expose all definitions!

-- TODO: revisit and fix this once the dust has settled
set_option backward.isDefEq.respectTransparency false

-- Let M be a C^k real manifold modeled on (E, H), endowed with a Riemannian metric.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Compatible connections: a connection on `TM` is compatible with the metric on `M` iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all sufficiently nice vector fields `X`, `Y` and
`Z` on `M`. In our definition, we ask for this identity to at each `x : M`, whenever `X`, `Y` and
`Z` are differentiable at `x`.
The left hand side is the pushforward of the function `⟨Y, Z⟩` along the vector field `X`:
the left hand side at `x` is `df(X x)`, where `f := ⟨Y, Z⟩`. -/

variable {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

/-- The scalar product of two vector fields -/
noncomputable abbrev product (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun x ↦ inner ℝ (X x) (Y x)

-- `product` is C^k if X and Y are: this is shown in `Riemannian.lean`

local notation "⟪" X ", " Y "⟫" => product I X Y

-- Basic API for the product of two vector fields.
section product

omit [IsManifold I 2 M]
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
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left]

@[simp]
lemma product_add_right_apply (x) : ⟪X, Y + Y'⟫ x = ⟪X, Y⟫ x + ⟪X, Y'⟫ x := by
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left_apply]

@[simp] lemma product_neg_left : ⟪-X, Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

@[simp] lemma product_neg_right : ⟪X, -Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

lemma product_sub_left : ⟪X - X', Y⟫ = ⟪X, Y⟫ - ⟪X', Y⟫ := by
  ext x
  simp [product, inner_sub_left]

lemma product_sub_right : ⟪X, Y - Y'⟫ = ⟪X, Y⟫ - ⟪X, Y'⟫ := by
  ext x
  simp [product, inner_sub_right]

lemma product_smul_left (f : M → ℝ) : product I (f • X) Y = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

@[simp]
lemma product_smul_const_left (a : ℝ) : product I (a • X) Y = a • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

lemma product_smul_right (f : M → ℝ) : product I X (f • Y) = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

@[simp]
lemma product_smul_const_right (a : ℝ) : product I X (a • Y) = a • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

end product

-- These lemmas are necessary as my Lie bracket identities (assuming minimal differentiability)
-- only hold point-wise. They abstract the expanding and unexpanding of `product`.
omit [IsManifold I 2 M] in
lemma product_congr_left {x} (h : X x = X' x) : product I X Y x = product I X' Y x := by
  rw [product_apply, h, ← product_apply]

omit [IsManifold I 2 M] in
lemma product_congr_left₂ {x} (h : X x = X' x + X'' x) :
    product I X Y x = product I X' Y x + product I X'' Y x := by
  rw [product_apply, h, inner_add_left, ← product_apply]
omit [IsManifold I 2 M] in
lemma product_congr_right {x} (h : Y x = Y' x) : product I X Y x = product I X Y' x := by
  rw [product_apply, h, ← product_apply]

omit [IsManifold I 2 M] in
lemma product_congr_right₂ {x} (h : Y x = Y' x + Y'' x) :
    product I X Y x = product I X Y' x + product I X Y'' x := by
  rw [product_apply, h, inner_add_right, ← product_apply]

/- XXX: writing `hY.inner_bundle hZ` or writing `by apply MDifferentiable.inner_bundle hY hZ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundle x
inferred
  fun b ↦ inst✝⁷ -/
-- TODO: diagnose and fix this, and replace by `MDifferentiable(At).inner_bundle!

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {I} in
lemma MDifferentiable.inner_bundle' (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) : MDiff ⟪Y, Z⟫ :=
  MDifferentiable.inner_bundle hY hZ

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {I} in
lemma MDifferentiableAt.inner_bundle' {x} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt ⟪Y, Z⟫ x :=
  MDifferentiableAt.inner_bundle hY hZ

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `TM`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Local notation for a connection. Caution: `∇ Y, X` corresponds to `∇ₓ Y` in textbooks -/
local notation "∇" Y "," X => fun (x:M) ↦ cov Y x (X x)

/-- The function defining the metric or compatibility tensor `∇ g` -/
noncomputable def metricTensorFun (Y Z : Π x : M, TangentSpace I x) :
    Π (x : M), TangentSpace I x →L[ℝ] ℝ := fun x ↦
  letI b : TangentSpace I x →L[ℝ] ℝ := mfderiv% ⟪Y, Z⟫ x
  b - ((innerSL ℝ (Z x)) ∘L (cov Y x)) - ((innerSL ℝ (Y x)) ∘L (cov Z x))

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

variable {I} in
private lemma aux1 {x : M} {f : M → ℝ} {σ τ : (x : M) → TangentSpace I x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    metricTensorFun I cov (f • σ) τ x = f x • metricTensorFun I cov σ τ x := by
  unfold metricTensorFun
  rw [product_smul_left, cov.isCovariantDerivativeOn.leibniz hσ hf]
  ext X
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, Pi.smul_apply', map_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    coe_innerSL_apply, Pi.sub_apply, Pi.smul_apply, comp_apply]
  erw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  conv =>
    enter [1, 1, 2]
    erw [ContinuousLinearMap.add_apply]
  conv =>
    enter [1, 1, 2, 1]
    erw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
    inner_smul_right, mfderiv_smul (hσ.inner_bundle' hτ) hf]
  simp only [smul_eq_mul, Pi.mul_apply, fromTangentSpace, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  conv =>
    enter [1, 1, 1, 2, 2]
    dsimp [product]
    rw [real_inner_comm]
  rw [← sub_eq_zero]
  ring

variable {I} in
private lemma aux2 {x : M} (σ σ' τ : (x : M) → TangentSpace I x)
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hτ : MDiffAt (T% τ) x) :
    metricTensorFun I cov (σ + σ') τ x =
      metricTensorFun I cov σ τ x + metricTensorFun I cov σ' τ x := by
  simp only [metricTensorFun]
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
private lemma aux3 {x : M} {f : M → ℝ} {σ τ : (x : M) → TangentSpace I x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    metricTensorFun I cov σ (f • τ) x = f x • metricTensorFun I cov σ τ x := by
  unfold metricTensorFun
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
private lemma aux4 {x : M} (σ τ τ' : (x : M) → TangentSpace I x)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x) :
    metricTensorFun I cov σ (τ + τ') x =
      metricTensorFun I cov σ τ x + metricTensorFun I cov σ τ' x := by
  unfold metricTensorFun
  ext X
  simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.coe_sub',
    ContinuousLinearMap.coe_comp', coe_innerSL_apply, Pi.sub_apply, comp_apply,
    ContinuousLinearMap.add_apply]
  rw [product_add_right, mfderiv_add (hσ.inner_bundle' hτ) (hσ.inner_bundle' hτ'),
    cov.isCovariantDerivativeOn.add hτ hτ']
  dsimp
  rw [inner_add_right]
  erw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  /- TODO: proof used to be done before merging rc4; was:
  conv =>
    enter [2, 2, 1, 2]
    erw [ContinuousLinearMap.comp_apply]
  rw [innerSL_apply_apply]
  conv =>
    enter [2, 2, 1, 2]
    erw [innerSL_apply_apply]
  module -/
  sorry
  -- set A := mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ⟫ x
  -- set A' := mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ'⟫ x
  -- set C := inner ℝ (σ x) ((cov τ x) X)
  -- set C' := inner ℝ (σ x) ((cov τ' x) X)
  -- set D := (cov σ x) X

variable {I} in
/-- The tensor `∇ g` defined by a connection `∇` on a Riemannian manifold `(M, g)`. -/
@[no_expose] noncomputable def MetricTensor [FiniteDimensional ℝ E] (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  mk2TensorAt I E E (metricTensorFun I cov)
    (fun _f _σ _τ hf hσ hτ ↦ aux1 cov hf hσ hτ)
    (fun σ σ' τ hσ hσ' hτ ↦ aux2 cov σ σ' τ hσ hσ' hτ)
    (fun _f _σ _τ hf hσ hτ ↦ aux3 cov hf hσ hτ)
    (fun σ τ τ' hσ hτ hτ' ↦ aux4 cov σ τ τ' hσ hτ hτ')

-- TODO: should we have ∇ X Y and ∇ X Z instead?
variable {I} in
theorem metricTensor_apply [FiniteDimensional ℝ E] (x : M)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MetricTensor cov x (Y x) (Z x) (X x) =
    fromTangentSpace _ (mfderiv% ⟪Y, Z⟫ x (X x)) - ⟪∇ Y, X, Z⟫ x - ⟪Y, ∇ Z, X⟫ x := by
  unfold MetricTensor
  rw [mk2TensorAt_apply _ _ _ _ _ _ hY hZ]
  simp only [metricTensorFun, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp',
    coe_innerSL_apply, Pi.sub_apply, comp_apply]
  conv =>
    enter [1, 1]
    erw [ContinuousLinearMap.sub_apply]
  conv =>
    enter [1, 1, 2]
    erw [ContinuousLinearMap.comp_apply]
  simp [product, real_inner_comm, fromTangentSpace]

variable {I} in
theorem metricTensor_apply_extend [FiniteDimensional ℝ E] (x : M) (X₀ Y₀ Z₀ : TangentSpace I x) :
    MetricTensor cov x Y₀ Z₀ X₀ =
      fromTangentSpace _ (mfderiv% ⟪(extend E Y₀), (extend E Z₀)⟫ x X₀)
        - ⟪∇ extend E Y₀, (extend E X₀), extend E Z₀⟫ x
        - ⟪extend E Y₀, ∇ extend E Z₀, (extend E X₀)⟫ x := by
  simpa [extend_apply_self] using metricTensor_apply cov x
    (X := extend E X₀) (mdifferentiableAt_extend I E Y₀) (mdifferentiableAt_extend I E Z₀)

/-- Predicate saying for a connection `∇` on a Riemannian manifold `(M, g)` to be compatible with
the ambient metric, i.e. for all differentiable` vector fields `X`, `Y` and `Z` on `M`, we have
`X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩`. -/
def IsCompatible [FiniteDimensional ℝ E] : Prop := MetricTensor cov = 0

-- Auxiliary computation for `IsCompatible_apply`.
-- TODO: inlining this lemma does not work
private lemma isCompatible_apply_aux {A B C : ℝ} (h : A - B - C = 0) : A = B + C := by grind

-- TODO: give a better name; maybe inline?
variable {I} in
lemma isCompatible_apply [FiniteDimensional ℝ E] (hcov : cov.IsCompatible) {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mfderiv% ⟪Y, Z⟫ x (X x) = ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ Z, X⟫ x := by
  rw [IsCompatible] at hcov
  have : MetricTensor cov x (Y x) (Z x) (X x) = 0 := by simp [hcov]
  rw [metricTensor_apply cov x hY hZ] at this
  change (fromTangentSpace _ ((mfderiv I 𝓘(ℝ, ℝ) ⟪Y, Z⟫ x) (X x))) = _
  exact isCompatible_apply_aux this

lemma isCompatible_iff [FiniteDimensional ℝ E] :
    cov.IsCompatible ↔ ∀ {x : M} {X Y Z : (x : M) → TangentSpace I x}
      (_hX : MDiffAt (T% X) x) (_hY : MDiffAt (T% Y) x) (_hZ : MDiffAt (T% Z) x),
      mfderiv% ⟪Y, Z⟫ x (X x) = ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ Z, X⟫ x := by
  refine ⟨fun hcov x X Y Z hX hY hZ ↦ cov.isCompatible_apply hcov hY hZ, fun h ↦ ?_⟩
  unfold IsCompatible
  ext x X₀ Y₀ Z₀
  rw [metricTensor_apply_extend, sub_sub, sub_eq_iff_eq_add']
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, add_zero]
  convert h (mdifferentiableAt_extend I E Z₀) (mdifferentiableAt_extend I E X₀)
    (mdifferentiableAt_extend I E Y₀)
  simp [fromTangentSpace, extend_apply_self]

end CovariantDerivative
