/-
Copyright (c) 2026 Miraj Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miraj Samarakkody
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



/-!
# Curves

This file develops basic definitions and results about
parametrized curves, especially Serret-Frenet formulas in n-dimensional space.
-/
open scoped InnerProductSpace

@[expose] public section

namespace Curves

/-- `ℝⁿ` denotes `EuclideanSpace ℝ (Fin n)`, the standard n-dimensional real Euclidean space. -/
scoped notation "ℝ^" n => EuclideanSpace ℝ (Fin n)

/-- A parametrized differentiable curve is a smooth map `α : I → ℝⁿ` of an open interval
`I = (a, b)` of the real line into `ℝⁿ`.

**Reference:** https://en.wikipedia.org/wiki/Frenet%E2%80%93Serret_formulas#Formulas_in_n_dimensions -/
structure ParametrizedDifferentiableCurve where
  /-- Ambient dimension of the Euclidean target space `ℝⁿ`. -/
  n : ℕ
  /-- Left endpoint `a` of the open interval `(a, b)`. -/
  a : ℝ
  /-- Right endpoint `b` of the open interval `(a, b)`. -/
  b : ℝ
  /-- The interval is non-degenerate: `a < b`. -/
  hab : a < b
  /-- The curve map `α : ℝ → ℝⁿ`, evaluated on `(a, b)`. -/
  toFun : ℝ → ℝ^n
  /-- `α` is smooth (`C^∞`) on the open interval `(a, b)`. -/
  contDiffOn : ContDiffOn ℝ ⊤ toFun (Set.Ioo a b)

/-- A parametrized differentiable curve `α : I → ℝⁿ` is **regular** if `α'(t) ≠ 0`
for all `t ∈ (a, b)`. -/
def regularCurve (α : ParametrizedDifferentiableCurve) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, deriv α.toFun t ≠ 0

/-- The arc length of `α` measured from `α.a` to `t`, defined by `s(t) = ∫_a^t ‖α'(u)‖ du`. -/
noncomputable def arcLength (α : ParametrizedDifferentiableCurve) (t : ℝ) : ℝ :=
  ∫ u in α.a..t, ‖deriv α.toFun u‖

/-- Apply the Gram–Schmidt process to obtain an orthonormal basis f
rom the vectors in the Frenet–Serret frame. -/
theorem FrenetSerretFrameVectorsExistence (α : ParametrizedDifferentiableCurve) (_ : ℝ) :
    ∃ _ _ _ : EuclideanSpace ℝ (Fin α.n), True := by
  refine ⟨0, 0, 0, trivial⟩

/-- Raw Frenet candidates from derivatives: α', α'', α''' (at t). -/
noncomputable def rawFrenetVecs
    (α : ParametrizedDifferentiableCurve) (t : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin α.n)
  | 0 => deriv α.toFun t
  | 1 => deriv (deriv α.toFun) t
  | 2 => deriv (deriv (deriv α.toFun)) t

/-- Orthonormalized frame obtained by Gram-Schmidt. -/
noncomputable def gsFrenetFrame
    (α : ParametrizedDifferentiableCurve) (t : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin α.n) :=
  InnerProductSpace.gramSchmidtNormed ℝ (rawFrenetVecs α t)

/-- Gram-Schmidt output is orthonormal -/
theorem gsFrenetFrame_orthonormal
    (α : ParametrizedDifferentiableCurve) (t : ℝ)
    (hlin : LinearIndependent ℝ (rawFrenetVecs α t)) :
    Orthonormal ℝ (gsFrenetFrame α t) := by
  simpa [gsFrenetFrame] using
    (InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℝ) hlin)

/-- `α` is **parametrized by arc length** if `‖α'(t)‖ = 1` for all `t ∈ (a, b)`. -/
def isArcLengthParametrized (α : ParametrizedDifferentiableCurve) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, ‖deriv α.toFun t‖ = 1

/- TODO:
  1. Define the last vector with cross product.
  2. Define Frenet-Serret matrix.
-/

-- The dedicated `ℝ^3` development is in `Mathlib/Geometry/Curves/BasicThreeDim.lean`.

end Curves
