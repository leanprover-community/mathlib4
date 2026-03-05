/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Util.PrintSorries

/-!
# The Levi-Civita connection

This file will define the Levi-Civita connection on any Riemannian manifold.
Details to be written!

TODO: refactor this file, to make Levi-Civita take a Riemannian metric instead!


TODO: more generally, define a notion of metric connections (e.g., those whose parallel transport
is an isometry) and prove the Levi-Civita connection is a metric connection

-/

open Bundle Filter Function Module Topology

open scoped Bundle Manifold ContDiff

@[expose] public section -- TODO: think if we want to expose all definitions!

-- TODO: revisit and fix this once the dust has settled
set_option backward.isDefEq.respectTransparency false

-- Let M be a C^k real manifold modeled on (E, H), endowed with a Riemannian metric.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  -- don't need this assumption (yet?)
  -- [IsRiemannianManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Compatible connections: a connection on TM is compatible with the metric on M iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all vector fields X, Y and Z on `M`.
The left hand side is the pushforward of the function `⟨Y, Z⟩` along the vector field `X`:
the left hand side at `X` is `df(X x)`, where `f := ⟨Y, Z⟩`. -/

variable {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

/-- The scalar product of two vector fields -/
noncomputable abbrev product (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun x ↦ inner ℝ (X x) (Y x)
-- Riemannian.lean shows that `product` is C^k if X and Y are

local notation "⟪" X ", " Y "⟫" => product I X Y

-- Basic API for the product of two vector fields.
section product

omit [IsManifold I ∞ M]

lemma product_apply (x) : ⟪X, Y⟫ x = inner ℝ (X x) (Y x) := rfl

variable (X Y) in
lemma product_swap : ⟪Y, X⟫ = ⟪X, Y⟫ := by
  ext x
  apply real_inner_comm

variable (X) in
@[simp]
lemma product_zero_left : ⟪0, X⟫ = 0 := by
  ext x
  simp [product]

@[simp]
lemma product_zero_right : ⟪X, 0⟫ = 0 := by rw [product_swap, product_zero_left]

variable (X X' Y) in
lemma product_add_left : ⟪X + X', Y⟫ = ⟪X, Y⟫ + ⟪X', Y⟫ := by
  ext x
  simp [product, InnerProductSpace.add_left]

variable (X X' Y) in
@[simp]
lemma product_add_left_apply (x) : ⟪X + X', Y⟫ x = ⟪X, Y⟫ x + ⟪X', Y⟫ x := by
  simp [product, InnerProductSpace.add_left]

variable (X Y Y') in
lemma product_add_right : ⟪X, Y + Y'⟫ = ⟪X, Y⟫ + ⟪X, Y'⟫ := by
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left]

variable (X X' Y) in
@[simp]
lemma product_add_right_apply (x) : ⟪X, Y + Y'⟫ x = ⟪X, Y⟫ x + ⟪X, Y'⟫ x := by
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left_apply]

variable (X Y) in
@[simp] lemma product_neg_left : ⟪-X, Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

variable (X Y) in
@[simp] lemma product_neg_right : ⟪X, -Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

variable (X X' Y) in
lemma product_sub_left : ⟪X - X', Y⟫ = ⟪X, Y⟫ - ⟪X', Y⟫ := by
  ext x
  simp [product, inner_sub_left]

variable (X Y Y') in
lemma product_sub_right : ⟪X, Y - Y'⟫ = ⟪X, Y⟫ - ⟪X, Y'⟫ := by
  ext x
  simp [product, inner_sub_right]

variable (X Y) in
lemma product_smul_left (f : M → ℝ) : product I (f • X) Y = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

variable (X Y) in
@[simp]
lemma product_smul_const_left (a : ℝ) : product I (a • X) Y = a • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

variable (X Y) in
lemma product_smul_right (f : M → ℝ) : product I X (f • Y) = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

variable (X Y) in
@[simp]
lemma product_smul_const_right (a : ℝ) : product I X (a • Y) = a • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

end product

-- These lemmas are necessary as my Lie bracket identities (assuming minimal differentiability)
-- only hold point-wise. They abstract the expanding and unexpanding of `product`.
omit [IsManifold I ∞ M] in
lemma product_congr_left {x} (h : X x = X' x) : product I X Y x = product I X' Y x := by
  rw [product_apply, h, ← product_apply]

omit [IsManifold I ∞ M] in
lemma product_congr_left₂ {x} (h : X x = X' x + X'' x) :
    product I X Y x = product I X' Y x + product I X'' Y x := by
  rw [product_apply, h, inner_add_left, ← product_apply]
omit [IsManifold I ∞ M] in
lemma product_congr_right {x} (h : Y x = Y' x) : product I X Y x = product I X Y' x := by
  rw [product_apply, h, ← product_apply]

omit [IsManifold I ∞ M] in
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

local notation "∇" X "," Y => fun (x:M) ↦ cov X x (Y x)

noncomputable def myfun (Y Z : Π x : M, TangentSpace I x) :
    Π (x : M), TangentSpace I x →L[ℝ] ℝ := fun x ↦
  letI b : TangentSpace I x →L[ℝ] ℝ := mfderiv% ⟪Y, Z⟫ x
  b - ((innerSL ℝ (Z x)) ∘L (cov Y x)) - ((innerSL ℝ (Y x)) ∘L (cov Z x))

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

variable {I} in
private lemma aux1 {x : M} (f : M → ℝ) {σ τ : (x : M) → TangentSpace I x}
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    myfun I cov (f • σ) τ x = f x • myfun I cov σ τ x := by
  have hτ : MDiffAt (T% τ) x := sorry -- missing hypothesis?
  unfold myfun
  rw [product_smul_left]
  rw [cov.isCovariantDerivativeOn.leibniz hσ hf]
  ext X
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, Pi.smul_apply', map_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    coe_innerSL_apply, Pi.sub_apply, Pi.smul_apply, comp_apply]
  erw [ContinuousLinearMap.sub_apply]
  erw [ContinuousLinearMap.sub_apply]
  erw [ContinuousLinearMap.comp_apply]
  conv =>
    enter [1, 1, 2]
    erw [ContinuousLinearMap.add_apply]
  conv =>
    enter [1, 1, 2, 1]
    erw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.comp_apply]
  rw [innerSL_apply_apply]
  rw [innerSL_apply_apply]
  rw [ContinuousLinearMap.toSpanSingleton_apply]
  rw [inner_smul_right]
  rw [mfderiv_smul (hσ.inner_bundle' hτ) hf]
  simp only [smul_eq_mul, Pi.mul_apply, bar, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  conv =>
    enter [1, 1, 1, 2, 2]
    dsimp [product]
    rw [real_inner_comm]
  rw [← sub_eq_zero]
  ring

variable {I} in
private lemma aux2 {x : M} (σ σ' τ : (x : M) → TangentSpace I x)
    (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x) :
    myfun I cov (σ + σ') τ x = myfun I cov σ τ x + myfun I cov σ' τ x := by
  have hτ : MDiffAt (T% τ) x := sorry -- missing hypothesis?
  simp only [myfun]
  ext X
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp', coe_innerSL_apply,
    Pi.sub_apply, comp_apply, ContinuousLinearMap.add_apply]
  rw [product_add_left,
    mfderiv_add (hσ.inner_bundle' hτ) (hσ'.inner_bundle' hτ),
    cov.isCovariantDerivativeOn.addσ hσ hσ',
    ContinuousLinearMap.comp_add, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    ContinuousLinearMap.add_apply, Pi.add_apply, inner_add_left]
  -- set A := mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ⟫ x
  -- set A' := mfderiv I 𝓘(ℝ, ℝ) ⟪σ', τ⟫ x
  -- set B := ((innerSL ℝ) (τ x)).comp (cov σ x)
  -- set B' := ((innerSL ℝ) (τ x)).comp (cov σ' x)
  -- set C := inner ℝ (σ x) ((cov τ x) X)
  -- set C' := inner ℝ (σ' x) ((cov τ x) X)
  erw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply]
  -- bug: abel fails, but module works
  module

variable {I} in
private lemma aux3 {x : M } (f : M → ℝ) {σ τ : (x : M) → TangentSpace I x}
    (hf : MDiffAt f x)
    (hτ : MDiffAt (T% τ) x) :
    myfun I cov σ (f • τ) x = f x • myfun I cov σ τ x := by
  -- TODO: should be similar to aux1!
  simp only [myfun]
  ext X
  dsimp
  rw [map_smul (innerSL ℝ) (f x) (τ x), product_smul_right]
  have hσ : MDiffAt (T% σ) x := sorry -- missing hypothesis?
  have aux := mfderiv_smul (s := f) (f := ⟪σ, τ⟫) (I := I) (x := x) (hσ.inner_bundle' hτ) hf
  set A := (f x • (innerSL ℝ) (τ x)).comp (cov σ x)
  set B := mfderiv I 𝓘(ℝ, ℝ) (f • ⟪σ, τ⟫) x
  -- issue: A and B live in different tangent spaces, so cannot simply expand and apply aux...
  -- next steps: apply the Leibniz rule, collect the other terms and suffer some more
  sorry

-- TODO: investigate why this takes so long!
set_option maxHeartbeats 400000 in
variable {I} in
private lemma aux4 {x : M} (σ τ τ' : (x : M) → TangentSpace I x)
    (hτ : MDiffAt (T% τ) x)
    (hτ' : MDiffAt (T% τ') x) :
    myfun I cov σ (τ + τ') x = myfun I cov σ τ x + myfun I cov σ τ' x := by
  have hσ : MDiffAt (T% σ) x := sorry -- missing hypothesis!
  unfold myfun
  ext X
  simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.coe_sub',
    ContinuousLinearMap.coe_comp', coe_innerSL_apply, Pi.sub_apply, comp_apply,
    ContinuousLinearMap.add_apply]
  rw [product_add_right, mfderiv_add (hσ.inner_bundle' hτ) (hσ.inner_bundle' hτ'),
    cov.isCovariantDerivativeOn.addσ hτ hτ']
  dsimp
  rw [inner_add_right]
  erw [ContinuousLinearMap.sub_apply]
  erw [ContinuousLinearMap.sub_apply]
  erw [ContinuousLinearMap.add_apply]
  erw [ContinuousLinearMap.comp_apply]
  conv =>
    enter [2, 2, 1, 2]
    erw [ContinuousLinearMap.comp_apply]
  erw [innerSL_apply_apply]
  conv =>
    enter [2, 2, 1, 2]
    erw [innerSL_apply_apply]
  -- set A := mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ⟫ x
  -- set A' := mfderiv I 𝓘(ℝ, ℝ) ⟪σ, τ'⟫ x
  -- set C := inner ℝ (σ x) ((cov τ x) X)
  -- set C' := inner ℝ (σ x) ((cov τ' x) X)
  -- set D := (cov σ x) X
  module

variable {I} in
/-- Given a connecion `∇` on `(M, g)`, the tensor `∇ g`. -/
@[no_expose] noncomputable def MetricTensor [FiniteDimensional ℝ E] (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  mk2TensorAt I E (myfun I cov)
    (fun f _σ _τ hf hσ ↦ aux1 cov f hf hσ)
    (fun σ σ' τ hσ hσ' ↦ aux2 cov σ σ' τ hσ hσ')
    (fun f _σ _τ hf hτ ↦ aux3 cov f hf hτ)
    (fun σ τ τ' hτ hτ' ↦ aux4 cov σ τ τ' hτ hτ')

/-- Predicate saying for a connection `∇` on a Riemannian manifold `(M, g)` to be compatible with
the ambient metric, i.e. for all differentiable` vector fields `X`, `Y` and `Z` on `M`, we have
`X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩`. -/
def IsCompatible [FiniteDimensional ℝ E] : Prop := MetricTensor cov = 0

lemma IsCompatible_apply [FiniteDimensional ℝ E] (hcov : cov.IsCompatible) {x : M} :
    mfderiv% ⟪Y, Z⟫ x (X x) = ⟪∇ X, Y, Z⟫ x + ⟪Y, ∇ X, Z⟫ x := sorry

/-- A covariant derivative on a Riemannian bundle `TM` is called the **Levi-Civita connection**
iff it is torsion-free and compatible with `g`.
Note that the bundle metric on `TM` is implicitly hidden in this definition. See `TODO` for a
version depending on a choice of Riemannian metric on `M`.
-/
def IsLeviCivitaConnection [FiniteDimensional ℝ E] : Prop := cov.IsCompatible ∧ cov.IsTorsionFree

variable (X Y Z) in
/-- The first term in the definition of the candidate Levi-Civita connection:
`rhs_aux I X Y Z = X ⟨Y, Z⟩ = x ↦ d(⟨Y, Z⟩)_x (X x)`.

This definition contains mild defeq abuse, which is invisible on paper:
The function `⟨Y, Z⟩` maps `M` into `ℝ`, hence its differential at a point `x` maps `T_p M`
to an element of the tangent space of `ℝ`. A summand `⟨Y, [X, Z]⟩`, however, yields an honest
real number: Lean complains that these have different types.
Fortunately, `ℝ` is defeq to its own tangent space; casting `rhs_aux` to the real numbers
allows the addition to type-check. -/
noncomputable abbrev rhs_aux : M → ℝ := fun x ↦ (mfderiv% ⟪Y, Z⟫ x (X x))

section rhs_aux

variable (Y Z) in
omit [IsManifold I ∞ M] in
lemma rhs_aux_swap : rhs_aux I X Y Z = rhs_aux I X Z Y := by
  ext x
  simp only [rhs_aux]
  congr 2
  exact product_swap I Z Y

omit [IsManifold I ∞ M] in
variable (X X' Y Z) in
lemma rhs_aux_addX : rhs_aux I (X + X') Y Z = rhs_aux I X Y Z + rhs_aux I X' Y Z := by
  ext x
  simp [rhs_aux]

variable {x : M}

variable (X) in
@[simp]
lemma rhs_aux_addY_apply (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X (Y + Y') Z x = rhs_aux I X Y Z x + rhs_aux I X Y' Z x := by
  simp only [rhs_aux]
  rw [product_add_left, mfderiv_add (hY.inner_bundle' hZ) (hY'.inner_bundle' hZ)]
  simp; congr

variable (X) in
lemma rhs_aux_addY (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    rhs_aux I X (Y + Y') Z = rhs_aux I X Y Z + rhs_aux I X Y' Z := by
  ext x
  exact rhs_aux_addY_apply I X (hY x) (hY' x) (hZ x)

variable (X) in
@[simp]
lemma rhs_aux_addZ_apply (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
  rhs_aux I X Y (Z + Z') x = rhs_aux I X Y Z x + rhs_aux I X Y Z' x := by
  unfold rhs_aux
  rw [product_add_right, mfderiv_add (hY.inner_bundle' hZ) (hY.inner_bundle' hZ')]; simp; congr

variable (X) in
lemma rhs_aux_addZ (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    rhs_aux I X Y (Z + Z') = rhs_aux I X Y Z + rhs_aux I X Y Z' := by
  ext x
  exact rhs_aux_addZ_apply I X (hY x) (hZ x) (hZ' x)

omit [IsManifold I ∞ M] in
variable (X Y Z) in
lemma rhs_aux_smulX_apply (f : M → ℝ) (x) : rhs_aux I (f • X) Y Z x = f x • rhs_aux I X Y Z x := by
  simp [rhs_aux]

omit [IsManifold I ∞ M] in
variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  ext x
  exact rhs_aux_smulX_apply ..

variable (X) in
lemma rhs_aux_smulY_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X (f • Y) Z x = f x • rhs_aux I X Y Z x + A x • ⟪Y, Z⟫ x := by
  rw [rhs_aux, product_smul_left, mfderiv_smul (hY.inner_bundle' hZ) hf]

variable (X) in
lemma rhs_aux_smulY {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X (f • Y) Z = f • rhs_aux I X Y Z + A • ⟪Y, Z⟫ := by
  ext x
  simp [rhs_aux_smulY_apply I X (hf x) (hY x) (hZ x)]

variable (X) in
lemma rhs_aux_smulY_const_apply {a : ℝ} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X (a • Y) Z x = a • rhs_aux I X Y Z x := by
  let f : M → ℝ := fun _ ↦ a
  have h1 : rhs_aux I X (a • Y) Z x = rhs_aux I X (f • Y) Z x := by simp only [f]; congr
  rw [h1, rhs_aux_smulY_apply I X mdifferentiableAt_const hY hZ]
  simp [mfderiv_const]

variable (X) in
lemma rhs_aux_smulY_const {a : ℝ} (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    rhs_aux I X (a • Y) Z = a • rhs_aux I X Y Z := by
  ext x
  apply rhs_aux_smulY_const_apply I X (hY x) (hZ x)

variable (X) in
lemma rhs_aux_smulZ_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X Y (f • Z) x = f x • rhs_aux I X Y Z x + A x • ⟪Y, Z⟫ x := by
  rw [rhs_aux_swap, rhs_aux_smulY_apply, rhs_aux_swap, product_swap]
  exacts [hf, hZ, hY]

variable (X) in
lemma rhs_aux_smulZ {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X Y (f • Z) = f • rhs_aux I X Y Z + A • ⟪Y, Z⟫ := by
  rw [rhs_aux_swap, rhs_aux_smulY, rhs_aux_swap, product_swap]
  exacts [hf, hZ, hY]

variable (X) in
lemma rhs_aux_smulZ_const_apply {a : ℝ} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X Y (a • Z) x = a • rhs_aux I X Y Z x := by
  let f : M → ℝ := fun _ ↦ a
  have h1 : rhs_aux I X Y (a • Z) x = rhs_aux I X Y (f • Z) x := by simp only [f]; congr
  rw [h1, rhs_aux_smulZ_apply I X mdifferentiableAt_const hY hZ]
  simp [mfderiv_const]

variable (X) in
lemma rhs_aux_smulZ_const {a : ℝ} (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    rhs_aux I X Y (a • Z) = a • rhs_aux I X Y Z := by
  ext x
  exact rhs_aux_smulZ_const_apply I X (hY x) (hZ x)

end rhs_aux

variable {x : M}

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If ∇ is a Levi-Civita connection on `TM`, then
`2 ⟨∇ X Y, Z⟩ = leviCivitaRhs' I X Y Z` for all vector fields `Z`. -/
noncomputable def leviCivitaRhs' : M → ℝ :=
  rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y
  - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
  - ⟪Z, (VectorField.mlieBracket I Y X)⟫
  + ⟪X, (VectorField.mlieBracket I Z Y)⟫

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If `∇` is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivitaRhs I X Y Z` for all smooth vector fields `X`, `Y` and `Z`. -/
noncomputable def leviCivitaRhs : M → ℝ := (1 / 2 : ℝ) • leviCivitaRhs' I X Y Z

omit [IsManifold I ∞ M] in
lemma leviCivitaRhs_apply : leviCivitaRhs I X Y Z x = (1 / 2 : ℝ) • leviCivitaRhs' I X Y Z x :=
  rfl

section leviCivitaRhs

@[simp]
lemma leviCivitaRhs'_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I (X + X') Y Z x =
      leviCivitaRhs' I X Y Z x + leviCivitaRhs' I X' Y Z x := by
  simp only [leviCivitaRhs', rhs_aux_addX, Pi.add_apply, Pi.sub_apply]
  -- We have to rewrite back and forth: the Lie bracket is only additive at x,
  -- as we are only asking for differentiability at x.
  -- Fortunately, the `product_congr_right₂` lemma abstracts this very well.
  rw [product_congr_right₂ I (VectorField.mlieBracket_add_right (V := Y) hX hX'),
    product_congr_right₂ I (VectorField.mlieBracket_add_left (W := Z) hX hX'),
    product_add_left_apply, rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  abel

lemma leviCivitaRhs'_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs' I (X + X') Y Z =
      leviCivitaRhs' I X Y Z + leviCivitaRhs' I X' Y Z := by
  ext x
  simp [leviCivitaRhs'_addX_apply _ (hX x) (hX' x) (hY x) (hZ x)]

lemma leviCivitaRhs_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I (X + X') Y Z x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X' Y Z x := by
  simp [leviCivitaRhs, leviCivitaRhs'_addX_apply I hX hX' hY hZ, left_distrib]

lemma leviCivitaRhs_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I (X + X') Y Z = leviCivitaRhs I X Y Z + leviCivitaRhs I X' Y Z := by
  ext x
  simp [leviCivitaRhs_addX_apply _ (hX x) (hX' x) (hY x) (hZ x)]

open VectorField

variable {I} in
lemma leviCivitaRhs'_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I (f • X) Y Z x = f x • leviCivitaRhs' I X Y Z x := by
  unfold leviCivitaRhs'
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_smulX, rhs_aux_smulY_apply, rhs_aux_smulZ_apply] <;> try assumption
  -- TODO: add the right congr_right lemma to avoid the product_apply, ← product_apply dance!
  simp only [product_apply, mlieBracket_smul_left (W := Z) hf hX,
    mlieBracket_smul_right (V := Y) hf hX, inner_add_right]
  -- Combining this line with the previous one fails.
  simp only [← product_apply, neg_smul, inner_neg_right]
  have h1 :
      letI dfZ : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x);
      inner ℝ (Y x) ((mfderiv I 𝓘(ℝ, ℝ) f x) (Z x) • X x) = dfZ * ⟪X, Y⟫ x := by
    simp only [product]
    rw [← real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_comm]
  have h2 :
      letI dfZ : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x);
      inner ℝ (Z x) ((mfderiv I 𝓘(ℝ, ℝ) f x) (Y x) • X x) = dfZ * ⟪Z, X⟫ x := by
    simp only [product]
    rw [← real_inner_smul_left, real_inner_smul_right, real_inner_smul_left]
  simp only [h1, h2]
  set dfY : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)
  set dfZ : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x)
  have h3 : ⟪f • X, mlieBracket I Z Y⟫ x = f x * ⟪X, mlieBracket I Z Y⟫ x := by
    rw [product_apply, Pi.smul_apply', real_inner_smul_left]
  have h4 : inner ℝ (Z x) (f x • mlieBracket I Y X x) = f x * ⟪Z, mlieBracket I Y X⟫ x := by
    rw [product_apply, real_inner_smul_right]
  rw [real_inner_smul_right (Y x), h3]--, h4]
  -- set A := ⟪Y, mlieBracket I X Z⟫ with hA
  -- set B := ⟪Z, mlieBracket I X Y⟫
  -- set C := ⟪X, mlieBracket I Z Y⟫
  -- set R := dfZ * ⟪X, Y⟫ x with hR
  -- set R' := dfY * ⟪Z, X⟫ x with hR'
  -- set E := rhs_aux I X Y Z x
  -- set F := rhs_aux I Y Z X x
  -- set G := rhs_aux I Z X Y x
  -- Push all applications of `x` inwards, then it's indeed obvious.
  simp
  ring_nf
  congr

variable {I} in
lemma leviCivitaRhs_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I (f • X) Y Z x = f x • leviCivitaRhs I X Y Z x := by
  simp only [leviCivitaRhs, one_div, Pi.smul_apply, smul_eq_mul]
  simp_rw [leviCivitaRhs'_smulX_apply (I := I) hf hX hY hZ]
  rw [← mul_assoc, mul_comm (f x), smul_eq_mul]
  ring

variable {I} in
lemma leviCivitaRhs_smulX [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I (f • X) Y Z = f • leviCivitaRhs I X Y Z := by
  ext x
  exact leviCivitaRhs_smulX_apply (hf x) (hX x) (hY x) (hZ x)

lemma leviCivitaRhs'_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X (Y + Y') Z x = leviCivitaRhs' I X Y Z x + leviCivitaRhs' I X Y' Z x := by
  simp only [leviCivitaRhs', Pi.add_apply, Pi.sub_apply, product_add_left_apply]
  rw [rhs_aux_addX, rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  -- We have to rewrite back and forth: the Lie bracket is only additive at x,
  -- as we are only asking for differentiability at x.
  rw [product_congr_right₂ I (mlieBracket_add_left (W := X) hY hY')]
  rw [product_congr_right₂ I (VectorField.mlieBracket_add_right (V := Z) hY hY')]
  simp only [Pi.add_apply]
  abel

lemma leviCivitaRhs_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (Y + Y') Z x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X Y' Z x := by
  simp [leviCivitaRhs, leviCivitaRhs'_addY_apply I hX hY hY' hZ, left_distrib]

lemma leviCivitaRhs_addY [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I X (Y + Y') Z = leviCivitaRhs I X Y Z + leviCivitaRhs I X Y' Z := by
  ext x
  simp [leviCivitaRhs_addY_apply I (hX x) (hY x) (hY' x) (hZ x)]

variable {I} in
lemma leviCivitaRhs'_smulY_const_apply [CompleteSpace E] {a : ℝ}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X (a • Y) Z x = a • leviCivitaRhs' I X Y Z x := by
  simp only [leviCivitaRhs']
  simp only [product_smul_const_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [rhs_aux_smulY_const_apply I X hY hZ]
  -- TODO: clean up this proof!
  let f : M → ℝ := fun _ ↦ a
  have : rhs_aux I (a • Y) Z X x = a • rhs_aux I Y Z X x := by
    trans rhs_aux I (f • Y) Z X x
    · rfl
    rw [rhs_aux_smulX I Y (f := f) (Y := Z) (Z := X)]
    rfl
  rw [this, rhs_aux_smulZ_const_apply I _ hX hY]
  -- is there a better abstraction for "Lie bracket conv mode"?
  have : ⟪Z, mlieBracket I (a • Y) X⟫ x = a • ⟪Z, mlieBracket I Y X⟫ x := by
    simp_rw [product_apply, mlieBracket_const_smul_left (W := X) hY, inner_smul_right_eq_smul]
  rw [this]
  have aux2 : ⟪X, mlieBracket I Z (a • Y)⟫ x = a • ⟪X, mlieBracket I Z Y⟫ x := by
    simp_rw [product_apply,  mlieBracket_const_smul_right (V := Z) hY, inner_smul_right_eq_smul]
  rw [aux2]
  simp
  ring

variable {I} in
lemma leviCivitaRhs_smulY_const_apply [CompleteSpace E] {a : ℝ}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (a • Y) Z x = a • leviCivitaRhs I X Y Z x := by
  simp_rw [leviCivitaRhs, Pi.smul_apply]; rw [smul_comm]
  congr
  exact leviCivitaRhs'_smulY_const_apply hX hY hZ

variable {I} in
lemma leviCivitaRhs_smulY_const [CompleteSpace E] {a : ℝ}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I X (a • Y) Z = a • leviCivitaRhs I X Y Z := by
  ext x
  exact leviCivitaRhs_smulY_const_apply (hX x) (hY x) (hZ x)

lemma leviCivitaRhs'_smulY_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X (f • Y) Z x =
      f x • leviCivitaRhs' I X Y Z x + ((bar _).toFun <| mfderiv% f x (X x)) • 2 * ⟪Y, Z⟫ x := by
  simp only [leviCivitaRhs']
  simp_rw [rhs_aux_smulX I Y Z X f]
  simp only [product_smul_left, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]
  rw [rhs_aux_smulY_apply I X hf hY hZ, rhs_aux_smulZ_apply I Z hf hX hY]
  -- TODO: is there a better abstraction for this kind of "Lie bracket conv mode"?
  have h1 : ⟪Z, mlieBracket I (f • Y) X⟫ x =
      - (bar _).toFun (((mfderiv% f x) (X x))) • ⟪Z, Y⟫ x + f x • ⟪Z, mlieBracket I Y X⟫ x := by
    simp_rw [product_apply, mlieBracket_smul_left (W := X) hf hY, inner_add_right]
    congr
    · simp only [neg_smul, inner_neg_right, bar, AddHom.toFun_eq_coe, AddHom.coe_mk, smul_eq_mul,
      neg_mul, neg_inj]
      rw [real_inner_smul_right]
    · rw [inner_smul_right_eq_smul]
  have h2 : ⟪X, mlieBracket I Z (f • Y)⟫ x =
      (bar _).toFun (((mfderiv% f x) (Z x))) • ⟪X, Y⟫ x + f x • ⟪X, mlieBracket I Z Y⟫ x := by
    simp_rw [product_apply, mlieBracket_smul_right (V := Z) hf hY, inner_add_right]
    congr
    · simp only [bar, AddHom.toFun_eq_coe, AddHom.coe_mk, smul_eq_mul]; rw [real_inner_smul_right]
    · rw [inner_smul_right_eq_smul]
  rw [h1, h2, product_swap I Y Z]
  set A := rhs_aux I X Y Z x
  set B := rhs_aux I Y Z X x
  set C := rhs_aux I Z X Y x
  set D := ⟪Y, mlieBracket I X Z⟫ x
  set E := ⟪Z, mlieBracket I Y X⟫ x
  set F := ⟪X, mlieBracket I Z Y⟫ x
  set G1 := ⟪Y, Z⟫ x
  set G2 := ⟪X, Y⟫ x
  set dfx := (mfderiv I 𝓘(ℝ, ℝ) f x)
  set H := (bar (f x)) (dfx (X x)) with H_eq
  set K := (bar (f x)) (dfx (Z x)) with K_eq
  change f x * A + (bar _).toFun (dfx (X x)) * G1 + f x * B
    - (f x * C + (bar _).toFun (dfx (Z x)) * G2)
    - f x * D - (-H * G1 + f x * E) + (K * G2 + f x * F) = _
  dsimp
  rw [← H_eq, ← K_eq]
  ring

lemma leviCivitaRhs_smulY_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (f • Y) Z x =
      f x • leviCivitaRhs I X Y Z x + ((bar _).toFun <| mfderiv% f x (X x)) • ⟪Y, Z⟫ x := by
  simp only [leviCivitaRhs, Pi.smul_apply, leviCivitaRhs'_smulY_apply I hf hX hY hZ]
  rw [smul_add, smul_comm]
  congr 1
  rw [← smul_eq_mul]
  dsimp
  field_simp

lemma leviCivitaRhs'_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivitaRhs' I X Y (Z + Z') x =
      leviCivitaRhs' I X Y Z x + leviCivitaRhs' I X Y Z' x := by
  simp only [leviCivitaRhs', rhs_aux_addX, Pi.add_apply, Pi.sub_apply, product_add_left_apply]
  rw [product_congr_right₂ I (VectorField.mlieBracket_add_right (V := X) hZ hZ'),
    product_congr_right₂ I (VectorField.mlieBracket_add_left (W := Y) hZ hZ'),
    rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  abel

lemma leviCivitaRhs'_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivitaRhs' I X Y (Z + Z') =
      leviCivitaRhs' I X Y Z + leviCivitaRhs' I X Y Z' := by
  ext x
  exact leviCivitaRhs'_addZ_apply I (hX x) (hY x) (hZ x) (hZ' x)

lemma leviCivitaRhs_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivitaRhs I X Y (Z + Z') x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X Y Z' x := by
  simp [leviCivitaRhs, leviCivitaRhs'_addZ_apply I hX hY hZ hZ', left_distrib]

lemma leviCivitaRhs_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivitaRhs I X Y (Z + Z') = leviCivitaRhs I X Y Z + leviCivitaRhs I X Y Z' := by
  ext x
  exact leviCivitaRhs_addZ_apply I (hX x) (hY x) (hZ x) (hZ' x)

lemma leviCivitaRhs'_smulZ_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X Y (f • Z) x = f x • leviCivitaRhs' I X Y Z x := by
  simp only [leviCivitaRhs', rhs_aux_smulX, Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_smulY_apply _ _ hf hZ hX, rhs_aux_smulZ_apply _ _ hf hY hZ]
  -- Apply the product rule for the lie bracket.
  -- Let's encapsulate the going into the product and back out again.
  have h1 : ⟪Y, mlieBracket I X (f • Z)⟫ x =
      f x • ⟪Y, mlieBracket I X Z⟫ x + ⟪Y, mfderiv% f x (X x) • Z⟫ x := by
    rw [product_apply, VectorField.mlieBracket_smul_right hf hZ, inner_add_right, add_comm,
      inner_smul_right]
    congr
  have h2 : letI dfY : ℝ :=  (mfderiv% f x) (Y x);
      ⟪X, mlieBracket I (f • Z) Y⟫ x = - dfY • ⟪X, Z⟫ x + f x • ⟪X, mlieBracket I Z Y⟫ x := by
    rw [product_apply, VectorField.mlieBracket_smul_left hf hZ, inner_add_right, inner_smul_right,
      inner_smul_right]
    congr
  rw [h1, h2, product_smul_left, product_swap I X Z]
  erw [product_smul_right]
  simp
  -- set A := rhs_aux I X Y Z x
  -- set B := rhs_aux I Y Z X x
  -- set C := rhs_aux I Z X Y x
  -- set D := ⟪Y, mlieBracket I X Z⟫ x
  -- set E := ⟪Z, mlieBracket I Y X⟫ x with E_eq
  -- set F := ⟪X, mlieBracket I Z Y⟫ x
  -- letI dfX : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)
  -- set G := dfX * ⟪Y, Z⟫ x
  -- letI dfY : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)
  -- set H := dfY * ⟪X, Z⟫ x
  ring

lemma leviCivitaRhs'_smulZ [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs' I X Y (f • Z) = f • leviCivitaRhs' I X Y Z := by
  ext x
  exact leviCivitaRhs'_smulZ_apply I (hf x) (hX x) (hY x) (hZ x)

lemma leviCivitaRhs_smulZ [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I X Y (f • Z) = f • leviCivitaRhs I X Y Z := by
  simp only [leviCivitaRhs]
  rw [smul_comm, leviCivitaRhs'_smulZ I hf hX hY hZ]

lemma leviCivitaRhs_smulZ_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X Y (f • Z) x = f x * leviCivitaRhs I X Y Z x := by
  simp [leviCivitaRhs, leviCivitaRhs'_smulZ_apply I hf hX hY hZ]
  ring

end leviCivitaRhs

variable [FiniteDimensional ℝ E] in
variable (Y) in
lemma aux (h : cov.IsLeviCivitaConnection) {x : M}
    (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) : rhs_aux I X Y Z x =
    ⟪∇ X, Y, Z⟫ x + ⟪Y, ∇ Z, X⟫ x + ⟪Y, VectorField.mlieBracket I X Z⟫ x := by
  trans ⟪∇ X, Y, Z⟫ x + ⟪Y, ∇ X, Z⟫ x
  · apply cov.IsCompatible_apply I h.1
  · simp [← cov.isTorsionFree_iff.mp h.2 hX hZ, product, inner_sub_right]

variable {cov} in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
⟨∇ X Y, Z⟩ for all differentiable vector fields X, Y and Z, without reference to ∇. -/
lemma IsLeviCivitaConnection.eq_leviCivitaRhs [FiniteDimensional ℝ E]
    (h : cov.IsLeviCivitaConnection)
    {x : M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ⟪∇ X, Y, Z⟫ x = leviCivitaRhs I X Y Z x := by
  unfold leviCivitaRhs leviCivitaRhs'
  have eq1 := aux I Y cov h hX hZ
  have eq2 := aux I Z cov h hY hX
  have eq3 := aux I X cov h hZ hY
  simp [real_inner_comm, smul_eq_mul] at *
  linear_combination - (eq1 + eq2 - eq3) / 2

section

variable {I} in
/-- If two vector fields `X` and `X'` on `M` satisfy the relation `⟨X, Z⟩ = ⟨X', Z⟩` for all
vector fields `Z`, then `X = X'`. XXX up to differentiability? -/
-- TODO: is this true if E is infinite-dimensional? trace the origin of the `Fintype` assumptions!
lemma congr_of_forall_product [FiniteDimensional ℝ E]
    (h : ∀ Z : Π x : M, TangentSpace I x, ⟪X, Z⟫ = ⟪X', Z⟫) : X = X' := by
  ext1 x
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
  apply Φ.injective
  ext Z₀
  simpa [Φ, product] using congr($(h (_root_.extend I E Z₀)) x)

/-- The Levi-Civita connection on `(M, g)` is uniquely determined,
at least on differentiable vector fields. -/
-- (probably not everywhere, as addition rules apply only for differentiable vector fields?)
theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    -- almost, only agree on smooth functions
    cov X x (Y x) = cov' X x (Y x) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
  apply Φ.injective
  ext Z₀
  let Z := _root_.extend I E Z₀
  have hZ := mdifferentiableAt_extend I E Z₀ x
  suffices inner ℝ (cov X x (Y x)) (Z x) = inner ℝ (cov' X x (Y x)) (Z x) by simpa [Φ, Z]
  trans leviCivitaRhs I X Y Z x
  · rw [← hcov.eq_leviCivitaRhs I hX hY hZ]
  · rw [← hcov'.eq_leviCivitaRhs I hX hY hZ]

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

open Classical in
noncomputable def lcAux₀ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  mk2TensorAt I E (fun (X Z : Π x : M, TangentSpace I x) ↦
      if hX : MDiffAt (T% X) x then if hZ : MDiffAt (T% Z) x then
        leviCivitaRhs I X Y Z
      else 0 else 0) (x := x)
    (fun {f X Z} hf hX ↦ by
      dsimp
      rw [if_pos hX, if_pos]
      · split_ifs with hZ
        · exact leviCivitaRhs_smulX_apply hf hX hY hZ
        · simp
      · exact hf.smul_section hX)
    (fun {X₁ X₂ Z} hX₁ hX₂ ↦ by
      dsimp
      rw [if_pos hX₁, if_pos hX₂, if_pos]
      · split_ifs with hZ
        · exact leviCivitaRhs_addX_apply I hX₁ hX₂ hY hZ
        · simp
      · exact mdifferentiableAt_add_section hX₁ hX₂)
    (fun {f X Z} hf hZ ↦ by
      dsimp
      rw [if_pos hZ]
      nth_rw 2 [if_pos]
      · split_ifs with hX
        · exact leviCivitaRhs_smulZ_apply I hf hX hY hZ
        · simp
      · exact hf.smul_section hZ)
    (fun {X Z₁ Z₂} hZ₁ hZ₂ ↦ by
      dsimp
      rw [if_pos hZ₁, if_pos hZ₂]
      nth_rw 2 [if_pos]
      · split_ifs with hX
        · exact leviCivitaRhs_addZ_apply I hX hY hZ₁ hZ₂
        · simp
      · exact mdifferentiableAt_add_section hZ₁ hZ₂)

theorem lcAux₀_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    lcAux₀ I x hY (X x) (Z x) = leviCivitaRhs I X Y Z x := by
  unfold lcAux₀
  rw [mk2TensorAt_apply _ _ _ _ _ hX hZ, dif_pos hX, dif_pos hZ]

noncomputable def lcAux₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  -- use the musical isomorphism to produce a candidate ∇ Y as a (1,1)-tensor
  -- (rather than a 2-tensor)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (lcAux₀ I x hY)

theorem lcAux₁_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (lcAux₁ I x hY (X x)) (Z x) = leviCivitaRhs I X Y Z x := by
  simpa [lcAux₁] using lcAux₀_apply I hX hY hZ

open Classical in
noncomputable def lcAux [FiniteDimensional ℝ E]
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then lcAux₁ I x hY else 0

theorem lcAux_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (lcAux I Y x (X x)) (Z x) = leviCivitaRhs I X Y Z x := by
  unfold lcAux
  rw [dif_pos hY]
  simpa [lcAux] using lcAux₁_apply I hX hY hZ

lemma isCovariantDerivativeOn_lcAux [FiniteDimensional ℝ E] :
    IsCovariantDerivativeOn E (lcAux I (M := M)) where
  addσ {Y Y'} x hY hY' _ := by
    unfold lcAux
    rw [dif_pos hY, dif_pos hY', dif_pos (mdifferentiableAt_add_section hY hY')]
    unfold lcAux₁
    dsimp
    rw [← ContinuousLinearMap.comp_add]
    congr! 1
    simp only [lcAux₀]
    ext X₀ Y₀
    simp only [mk2TensorAt, IsBilinearMap.toContinuousLinearMap, IsBilinearMap.toLinearMap,
      dite_eq_ite, LinearMap.coe_toContinuousLinearMap', IsLinearMap.mk'_apply, LinearMap.mk₂_apply,
      ContinuousLinearMap.add_apply]
    rw [if_pos, if_pos, if_pos, if_pos, if_pos, if_pos]
    · apply leviCivitaRhs_addY_apply
      · exact mdifferentiable_extend ..
      · exact hY
      · exact hY'
      · exact mdifferentiable_extend ..
    · exact mdifferentiable_extend ..
    · exact mdifferentiable_extend ..
    · exact mdifferentiable_extend ..
    · exact mdifferentiable_extend ..
    · exact mdifferentiable_extend ..
    · exact mdifferentiable_extend ..
  leibniz {Y f x} hY hf _ := by
    unfold lcAux
    dsimp
    rw [dif_pos hY, dif_pos]
    · unfold lcAux₁
      dsimp
      rw [← ContinuousLinearMap.comp_smul]
      have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
      have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
      set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
      ext X₀
      apply Φ.injective
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, comp_apply,
        LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.toSpanSingleton_apply, map_add, map_smul]
      ext Z₀
      simp only [lcAux₀, mk2TensorAt, IsBilinearMap.toContinuousLinearMap,
        IsBilinearMap.toLinearMap, dite_eq_ite, LinearMap.coe_toContinuousLinearMap',
        IsLinearMap.mk'_apply, LinearMap.mk₂_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [if_pos, if_pos, if_pos, if_pos]
      · have key := leviCivitaRhs_smulY_apply I (X := _root_.extend I E X₀) (Y := Y)
          (Z := _root_.extend I E Z₀) (x := x) (f := f)
        convert key hf ?_ hY ?_
        · simp
        · simp [Φ, product]
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      · exact mdifferentiable_extend ..
      · exact mdifferentiable_extend ..
      · exact mdifferentiable_extend ..
      · exact mdifferentiable_extend ..
    exact MDifferentiableAt.smul_section hf hY

end

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
noncomputable def LeviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := lcAux I
  isCovariantDerivativeOn := isCovariantDerivativeOn_lcAux I

theorem leviCivitaConnection_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (LeviCivitaConnection I M Y x (X x)) (Z x) = leviCivitaRhs I X Y Z x :=
  lcAux_apply _ hX hY hZ

#exit
-- TODO: move this section to `Torsion.lean`
section

--omit [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
--omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- The **Christoffel symbol** of a covariant derivative on a set `U ⊆ M`
with respect to a local frame `(s_i)` on `U`: for each triple `(i, j, k)` of indices,
this is a function `Γᵢⱼᵏ : M → ℝ`, whose value outside of `U` is meaningless. -/
noncomputable def ChristoffelSymbol
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    {U : Set M} {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) : M → ℝ :=
  hs.coeff k (fun x ↦ f (s i) x (s j x))

-- special case of `foobar` below; needed?
lemma ChristoffelSymbol.sum_eq
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    {U : Set M} {ι : Type*} [Fintype ι] {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j : ι) (hx : x ∈ U) :
    f (s i) x (s j x) = ∑ k, (ChristoffelSymbol I f hs i j k x) • (s k) x := by
  simp only [ChristoffelSymbol]
  exact hs.coeff_sum_eq _ hx

variable {U : Set M}
  {f g : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {ι : Type*} {s : ι → (x : M) → TangentSpace I x}

-- Note that this result is false if `{s i}` is merely a local frame.
lemma eq_product_apply [Fintype ι]
    (hf : IsCovariantDerivativeOn E f U)
    (hs : IsOrthonormalFrameOn I E n s U)
    (i j k : ι) (hx : x ∈ U) :
    ChristoffelSymbol I f hs.toIsLocalFrameOn i j k x = inner ℝ (f (s i) x (s j x)) (s k x) := by
  -- Choose a linear order on ι: which one really does not matter for our result.
  have : LinearOrder ι := by
    choose r wo using exists_wellOrder _
    exact r
  have : LocallyFiniteOrderBot ι := by sorry
  rw [ChristoffelSymbol, hs.coeff_eq_inner' (f (s i) (s j)) hx k, real_inner_comm]

-- Lemma 4.3 in Lee, Chapter 5: first term still missing
lemma foobar [Fintype ι] [FiniteDimensional ℝ E] (hf : IsCovariantDerivativeOn E f U)
    (hs : IsLocalFrameOn I E 1 s U) {x : M} (hx : x ∈ U) :
    f X x (Y x) = ∑ k,
      letI S₁ := ∑ i, ∑ j, (hs.coeff i X) * (hs.coeff j Y) * (ChristoffelSymbol I f hs i j k)
      letI S₂ : M → ℝ := sorry -- first summand in Leibniz' rule!
      S₁ x • s k x := by
  have hY := hs.coeff_sum_eq Y hx
  -- should this be a separate lemma also?
  have : ∀ x ∈ U, Y x = ∑ i, (hs.coeff i) Y x • s i x := by
    intro x hx
    apply hs.coeff_sum_eq Y hx
  have : f X x (Y x) = f X (fun x ↦ ∑ i, (hs.coeff i) Y x • s i x) x := by
    -- apply `congr_σ_of_eventuallyEq` from Basic.lean (after restoring it)
    -- want U to be a neighbourhood of x to make this work
    sorry
  rw [this]
  -- straightforward computation: use linearity and Leibniz rule
  sorry

/- TODO: prove some basic properties, such as
- the Christoffel symbols are linear in cov
- if (s_i) is a smooth local frame on U, then cov is smooth on U iff each Christoffel symbol is (?)
- prove a `spec` equality
- deduce: two covariant derivatives are equal iff their Christoffel symbols are equal
-/

lemma _root_.IsCovariantDerivativeOn.congr_of_christoffelSymbol_eq [Fintype ι]
    [FiniteDimensional ℝ E] -- TODO: this is implied by Finite ι, right?
    (hf : IsCovariantDerivativeOn E f U) (hg : IsCovariantDerivativeOn E g U)
    (hs : IsLocalFrameOn I E n s U)
    (hfg : ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I g hs i j k x) :
    ∀ X Y : Π x : M, TangentSpace I x, ∀ x ∈ U, f X x (Y x) = g X x (Y x) := by
  have (i j : ι) : ∀ x ∈ U, f (s i) (s j) x = g (s i) (s j) x := by
    intro x hx
    rw [hs.eq_iff_coeff hx]
    exact fun k ↦ hfg i j k x hx
  intro X Y x hx
  -- use linearity (=formula for f in terms of Christoffel symbols) now, another separate lemma!
  sorry

/-- Two covariant derivatives on `U` are equal on `U` if and only if all of their
covariant derivatives w.r.t. some local frame on `U` are equal on `U`. -/
lemma _root_.IsCovariantDerivativeOn.congr_iff_christoffelSymbol_eq [Fintype ι]
    [FiniteDimensional ℝ E] -- TODO: this is implied by Finite ι, right?
    (hf : IsCovariantDerivativeOn E f U) (hg : IsCovariantDerivativeOn E g U)
    (hs : IsLocalFrameOn I E n s U) :
    (∀ X Y : Π x : M, TangentSpace I x, ∀ x ∈ U, f X x (Y x) = g X x (Y x)) ↔
    ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I g hs i j k x :=
  ⟨fun hfg _i _j _k _x hx ↦ hs.coeff_congr (hfg _ _ _ hx ) ..,
    fun h X Y x hx ↦ hf.congr_of_christoffelSymbol_eq I hg hs h X Y x hx⟩

-- TODO: global version for convenience, with an alias for the interesting direction!

variable (hs : IsLocalFrameOn I E n s U)

lemma christoffelSymbol_zero (U : Set M) {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) : ChristoffelSymbol I 0 hs i j k = 0 := by
  simp [ChristoffelSymbol]

@[simp]
lemma christoffelSymbol_zero_apply (U : Set M) {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) (x) : ChristoffelSymbol I 0 hs i j k x = 0 := by
  simp [christoffelSymbol_zero]

end

-- Lemma 4.3 in Lee, Chapter 5: first term still missing
variable {U : Set M} {ι : Type*} [Fintype ι] {s : ι → (x : M) → TangentSpace I x}
  {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}

-- errors: omit [IsContMDiffRiemannianBundle I 1 E fun x ↦ TangentSpace I x] in
/-- Let `{s i}` be a local frame on `U` such that `[s i, s j] = 0` on `U` for all `i, j`.
A covariant derivative on `U` is torsion-free on `U` iff for each `x ∈ U`,
the Christoffel symbols `Γᵢⱼᵏ` w.r.t. `{s i}` are symmetric. -/
lemma isTorsionFreeOn_iff_christoffelSymbols [CompleteSpace E] {ι : Type*} [Fintype ι]
    [FiniteDimensional ℝ E] -- TODO: this is implied by Finite ι, right?
    (hf : IsCovariantDerivativeOn E f U)
    {s : ι → (x : M) → TangentSpace I x} (hs : IsLocalFrameOn I E n s U)
    (hs'' : ∀ i j, ∀ x : U, VectorField.mlieBracket I (s i) (s j) x = 0) :
    IsTorsionFreeOn f U ↔
      ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I f hs j i k x := by
  rw [hf.isTorsionFreeOn_iff_localFrame (n := n) hs]
  have (i j : ι) {x} (hx : x ∈ U) :
      torsion f (s i) (s j) x = f (s i) x (s j x) - f (s j) x (s i x) := by
    simp [torsion, hs'' i j ⟨x, hx⟩]
  peel with i j
  refine ⟨?_, ?_⟩
  · intro h k x hx
    simp only [ChristoffelSymbol]
    apply hs.coeff_congr
    specialize h x hx
    rw [this i j hx, sub_eq_zero] at h
    exact h
  · intro h x hx
    rw [this i j hx, sub_eq_zero, hs.eq_iff_coeff hx]
    exact fun k ↦ h k x hx

-- Exercise 4.2(b) in Lee, Chapter 4
/-- A covariant derivative on `U` is torsion-free on `U` iff for each `x ∈ U` and
any local coordinate frame, the Christoffel symbols `Γᵢⱼᵏ` are symmetric.

TODO: figure out the right quantifiers here!
right now, I just have one fixed coordinate frame... will this do??
-/
lemma isTorsionFree_iff_christoffelSymbols' [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (hf : IsCovariantDerivativeOn E f U) :
    IsTorsionFreeOn f U ↔
      ∀ x ∈ U,
      -- Let `{s_i}` be the coordinate frame at `x`: this statement is false for arbitrary frames.
      -- TODO: does the following do what I want??
      letI cs := ChristoffelSymbol I f
          ((Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 (trivializationAt E _ x))
      ∀ i j k, cs i j k x = cs j i k x := by
  letI t := (trivializationAt E (fun (x : M) ↦ TangentSpace I x))
  have hs (x) :=
    ((Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 (t x))

  -- TODO: check that the Lie bracket of any two coordinate vector fields is zero!
  rw [isTorsionFreeOn_iff_christoffelSymbols (ι := (↑(Basis.ofVectorSpaceIndex ℝ E))) I hf]
  -- issues with quantifier order in the statement... prove both directions separately, at each x?
  repeat sorry

theorem LeviCivitaConnection.christoffelSymbol_symm [FiniteDimensional ℝ E] (x : M) :
    letI t := trivializationAt E (TangentSpace I) x;
    letI hs := (Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 t
    ∀ x', x' ∈ t.baseSet → ∀ (i j k : ↑(Basis.ofVectorSpaceIndex ℝ E)),
      ChristoffelSymbol I (LeviCivitaConnection I M) hs i j k x' =
        ChristoffelSymbol I (LeviCivitaConnection I M) hs j i k x' := by
  by_cases hE : Subsingleton E
  · have (y : M) (X : TangentSpace I y) : X = 0 := by
      have : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
      apply Subsingleton.eq_zero X
    have (X : Π y : M, TangentSpace I y) : X = 0 := sorry
    intro x'' hx'' i j k
    simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
    unfold lcCandidate
    simp only [lcAux, hE, ↓reduceDIte]

    letI t := trivializationAt E (TangentSpace I) x;
    letI hs := (Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 t
    have : ChristoffelSymbol I 0 hs i j k = 0 := christoffelSymbol_zero I t.baseSet hs i j k
    -- now, use a congruence result and the first `have`
    sorry
  -- Note that hs is not necessarily an orthonormal frame, so we cannot simply rewrite
  -- the Christoffel symbols as Γᵢⱼᵏ = ⟪∇ᵍ X Y, Z⟫`: however, the result we wants to prove boils
  -- down to proving the same.
  intro x' hx' i j
  set t := trivializationAt E (TangentSpace I) x
  set b := (Basis.ofVectorSpace ℝ E)
  set s := b.localFrame t
  set ι := ↑(Basis.ofVectorSpaceIndex ℝ E)
  -- Same computation as above; extract as lemma!
  let O : (x : M) → TangentSpace I x := fun x ↦ 0
  have need : ∀ i j, VectorField.mlieBracket I (s i) (s j) x' = O x' := sorry
  have aux : ∀ k, ⟪LeviCivitaConnection I M (s i) (s j), (s k)⟫ x'
      = ⟪LeviCivitaConnection I M (s j) (s i), (s k)⟫ x' := by
    intro k
    simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
    unfold lcCandidate
    rw [product_apply, product_apply]
    simp only [lcAux, hE, ↓reduceDIte]
    -- Choose a linear order on ι: which one really does not matter for our result.
    have : LinearOrder ι := by
      choose r wo using exists_wellOrder _
      exact r
    have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have : Nonempty ι := b.index_nonempty
    -- The linear ordering on the indexing set of `b` is only used in this proof,
    -- so our choice does not matter.
    have : LinearOrder ι := by
      choose r wo using exists_wellOrder _
      exact r
    have : Fintype ι := sorry
    -- why does this fail? are there two different orders in play?
    have : LocallyFiniteOrderBot ι := sorry
    have : ∑ k', inner ℝ
      (leviCivitaRhs I (s i) (s j)
          (b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k') x' •
          b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x')
      (s k x') =
       ∑ k', inner ℝ
        (leviCivitaRhs I (s j) (s i)
          (b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k') x' •
          b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x')
        (s k x') := by
      congr with k'
      simp only [leviCivitaRhs]
      set sij := b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x'
      rw [inner_smul_left, inner_smul_left]
      congr
      simp [leviCivitaRhs']
      set S := b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k'
      have need' : ∀ i, VectorField.mlieBracket I (s i) S x' = O x' := by
        -- expand the definition of Gram-Schmidt and use need and linearity
        sorry
      have need'' : ∀ i, VectorField.mlieBracket I S (s i) x' = O x' := by
        sorry -- swap and use need', or so
      rw [product_congr_right I (need i j), product_congr_right I (need j i),
        product_congr_right I (need' i), product_congr_right I (need'' i),
        product_congr_right I (need' j), product_congr_right I (need'' j),
        rhs_aux_swap I (s i) (s j), rhs_aux_swap I (s j) S, rhs_aux_swap I S (s i)]
      simp [O]
      abel
    -- now, just rewrite `inner` to take out a sum: same lemma twice
    convert this
    · sorry
    · sorry

  -- deduce the goal from `aux`
  sorry

lemma baz [FiniteDimensional ℝ E] : (LeviCivitaConnection I M).IsLeviCivitaConnection := by
  -- If `E` is trivial, the Levi-Civita connection is always zero and all proofs are trivial.
  by_cases hE : Subsingleton E
  · have (y : M) (X : TangentSpace I y) : X = 0 := by
      have : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
      apply Subsingleton.eq_zero X
    refine ⟨?_, ?_⟩
    · intro X Y Z x
      simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
      unfold lcCandidate
      simp [this]
    · simp only [isTorsionFree_def, LeviCivitaConnection, LeviCivitaConnection_aux]
      unfold lcCandidate torsion
      ext; simp [this]
  refine ⟨?_, ?_⟩
  · intro X Y Z x
    unfold LeviCivitaConnection LeviCivitaConnection_aux lcCandidate
    simp only [lcAux, hE, ↓reduceDIte]
    --simp [product_apply]
    sorry -- compatible
  · let s : M → Set M := fun x ↦ (trivializationAt E (fun (x : M) ↦ TangentSpace I x) x).baseSet
    apply (LeviCivitaConnection I M).of_isTorsionFreeOn_of_open_cover (s := s) ?_ (by aesop)
    intro x
    simp only [s]
    set t := fun x ↦ trivializationAt E (TangentSpace I : M → Type _) x with t_eq
    have : IsCovariantDerivativeOn E (LeviCivitaConnection I M) (t x).baseSet :=
      isCovariantDerivativeOn_lcCandidate _ (t x)
    rw [isTorsionFree_iff_christoffelSymbols' _ this]
    intro x' hx' i j k
    -- Now, compute christoffel symbols and be happy.
    have := LeviCivitaConnection.christoffelSymbol_symm I x  x' hx' i j k
    sorry -- almost there, except x vs x' convert this

end CovariantDerivative
