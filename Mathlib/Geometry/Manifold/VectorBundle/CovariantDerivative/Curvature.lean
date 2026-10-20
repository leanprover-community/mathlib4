/-
Copyright (c) 2026 Alex Korbonits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Korbonits
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! # The Riemann curvature of a covariant derivative on the tangent bundle

We define the Riemann curvature of a covariant derivative on the tangent bundle `TM` of a
manifold `M`, as an operator on vector fields:
`curvature cov X Y Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z`.

## Main definitions and results

* `CovariantDerivative.curvature`: the Riemann curvature of a covariant derivative on `TM`,
  as an operator on vector fields.
* `CovariantDerivative.curvature_swap`: the curvature is antisymmetric in its first two arguments.
* `CovariantDerivative.tensorialAt_curvature_fst`, `CovariantDerivative.tensorialAt_curvature_snd`:
  for a `C¹` covariant derivative and a `C²` vector field `Z`, the curvature is tensorial in its
  first two arguments.

## Implementation notes

We follow the convention `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`. Recall that in Mathlib
`cov σ x v` denotes `(∇_v σ) x`: the section being differentiated comes first.

The curvature is defined here as an operator on vector fields, not yet as a pointwise tensor.
Tensoriality in the third argument is a second-order statement: expanding `∇_X ∇_Y (f • Z)`
produces second derivatives of `f`, which cancel against `[X, Y] f` only by the derivation
property of the Lie bracket. The first two arguments, on the other hand, are tensorial in the
sense of `TensorialAt`.

Unlike `CovariantDerivative.torsion`, we do not develop an unbundled
(`IsCovariantDerivativeOn`) version: the unbundled theory exists to analyse global objects in
local trivializations, which is not yet needed for the curvature.

## TODO

* Prove tensoriality in the third argument.
* Package the curvature as a pointwise tensor.
* Prove the first and second Bianchi identities.
-/

@[expose] public noncomputable section

open Bundle Set NormedSpace FiberBundle VectorField
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

namespace CovariantDerivative

variable [IsManifold I 2 M] [CompleteSpace E]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  {X X' Y Y' Z : Π x : M, TangentSpace I x}

/-- The Riemann curvature of a covariant derivative on the tangent bundle, as an operator on
vector fields: `curvature cov X Y Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z`.

This quantity is tensorial in all three arguments (for the first two, see
`tensorialAt_curvature_fst` and `tensorialAt_curvature_snd`), so its value at `x` only depends on
the values `X x`, `Y x`, `Z x`. -/
def curvature (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun x ↦ cov (fun y ↦ cov Z y (Y y)) x (X x) - cov (fun y ↦ cov Z y (X y)) x (Y x)
    - cov Z x (mlieBracket I X Y x)

omit [CompleteSpace E] in
lemma curvature_apply :
    curvature cov X Y Z x = cov (fun y ↦ cov Z y (Y y)) x (X x)
      - cov (fun y ↦ cov Z y (X y)) x (Y x) - cov Z x (mlieBracket I X Y x) :=
  rfl

variable (X Z) in
omit [CompleteSpace E] in
@[simp]
lemma curvature_self : curvature cov X X Z = 0 := by
  funext x
  simp [curvature]

variable (X Y Z) in
omit [CompleteSpace E] in
/-- The Riemann curvature is antisymmetric in its first two arguments. -/
lemma curvature_swap : curvature cov X Y Z = - curvature cov Y X Z := by
  funext x
  rw [Pi.neg_apply, curvature_apply, curvature_apply, mlieBracket_swap_apply, map_neg]
  abel

/-- The Riemann curvature is tensorial in its first argument: multiplying `X` by a function `f`
multiplies `curvature cov X Y Z` at `x` by `f x`. -/
lemma curvature_smul_left {f : M → 𝕜} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x) :
    curvature cov (f • X) Y Z x = f x • curvature cov X Y Z x := by
  have h1 : (fun y ↦ cov Z y ((f • X) y)) = f • (fun y ↦ cov Z y (X y)) := by
    ext y
    simp
  rw [curvature_apply, curvature_apply, h1,
    cov.isCovariantDerivativeOnUniv.leibniz hXZ hf trivial,
    mlieBracket_smul_left hf hX]
  simp only [Pi.smul_apply', Pi.smul_apply, map_smul, map_add, add_apply,
    FunLike.coe_smul, ContinuousLinearMap.smulRight_apply]
  module

/-- The Riemann curvature is additive in its first argument. -/
lemma curvature_add_left (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x)
    (hX'Z : MDiffAt (T% (fun y ↦ cov Z y (X' y))) x) :
    curvature cov (X + X') Y Z x = curvature cov X Y Z x + curvature cov X' Y Z x := by
  have h1 : (fun y ↦ cov Z y ((X + X') y)) =
      (fun y ↦ cov Z y (X y)) + (fun y ↦ cov Z y (X' y)) := by
    ext y
    simp
  rw [curvature_apply, curvature_apply, curvature_apply, h1,
    cov.isCovariantDerivativeOnUniv.add hXZ hX'Z trivial,
    mlieBracket_add_left hX hX']
  simp only [Pi.add_apply, map_add, add_apply]
  abel

/-- The Riemann curvature is tensorial in its second argument: multiplying `Y` by a function `f`
multiplies `curvature cov X Y Z` at `x` by `f x`. -/
lemma curvature_smul_snd {f : M → 𝕜} (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x) :
    curvature cov X (f • Y) Z x = f x • curvature cov X Y Z x := by
  rw [curvature_swap, Pi.neg_apply, curvature_smul_left cov hf hY hYZ,
    curvature_swap cov Y X Z, Pi.neg_apply, smul_neg, neg_neg]

/-- The Riemann curvature is additive in its second argument. -/
lemma curvature_add_snd (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x)
    (hY'Z : MDiffAt (T% (fun y ↦ cov Z y (Y' y))) x) :
    curvature cov X (Y + Y') Z x = curvature cov X Y Z x + curvature cov X Y' Z x := by
  rw [curvature_swap, Pi.neg_apply, curvature_add_left cov hY hY' hYZ hY'Z,
    curvature_swap cov Y X Z, curvature_swap cov Y' X Z]
  simp only [Pi.neg_apply]
  abel

section tensorial

variable [ContMDiffCovariantDerivative cov 1]

omit [CompleteSpace E] in
/-- If `∇` is a `C¹` covariant derivative, `σ` is a `C²` vector field and `X` is a vector field
differentiable at `x`, then `∇_X σ` is differentiable at `x`. -/
lemma mdifferentiableAt_apply {σ : Π x : M, TangentSpace I x} (hσ : CMDiff 2 (T% σ))
    (hX : MDiffAt (T% X) x) : MDiffAt (T% (fun y ↦ cov σ y (X y))) x := by
  have h := (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 1)).contMDiff
    (σ := σ) (by rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]; exact hσ.contMDiffOn) x trivial
  exact ((contMDiffWithinAt_univ.mp h).mdifferentiableAt one_ne_zero).clm_bundle_apply hX

/-- For a `C¹` covariant derivative and a `C²` vector field `Z`, the curvature `R(X, Y) Z` at `x`
is tensorial in `X`. -/
lemma tensorialAt_curvature_fst (hZ : CMDiff 2 (T% Z)) (Y : Π x : M, TangentSpace I x) (x : M) :
    TensorialAt I E (fun X ↦ curvature cov X Y Z x) x where
  smul hf hX := cov.curvature_smul_left hf hX (cov.mdifferentiableAt_apply hZ hX)
  add hX hX' := cov.curvature_add_left hX hX' (cov.mdifferentiableAt_apply hZ hX)
    (cov.mdifferentiableAt_apply hZ hX')

/-- For a `C¹` covariant derivative and a `C²` vector field `Z`, the curvature `R(X, Y) Z` at `x`
is tensorial in `Y`. -/
lemma tensorialAt_curvature_snd (hZ : CMDiff 2 (T% Z)) (X : Π x : M, TangentSpace I x) (x : M) :
    TensorialAt I E (fun Y ↦ curvature cov X Y Z x) x where
  smul hf hY := cov.curvature_smul_snd hf hY (cov.mdifferentiableAt_apply hZ hY)
  add hY hY' := cov.curvature_add_snd hY hY' (cov.mdifferentiableAt_apply hZ hY)
    (cov.mdifferentiableAt_apply hZ hY')

end tensorial

end CovariantDerivative
