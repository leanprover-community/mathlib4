/-
Copyright (c) 2026 Seed Prover, Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seed Prover, Kim Morrison
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Koszul formula

This file proves the Koszul formula for a smooth torsion-free metric-compatible
covariant derivative on the tangent bundle of a Riemannian manifold.

For such a covariant derivative `cov`, the inner product `⟨∇_X Y, Z⟩` is determined
by the metric and Lie brackets via

`2 ⟨∇_X Y, Z⟩ = X·⟨Y, Z⟩ + Y·⟨X, Z⟩ − Z·⟨X, Y⟩`
`               − ⟨X, [Y, Z]⟩ − ⟨Y, [X, Z]⟩ + ⟨Z, [X, Y]⟩`.

This formula implies the uniqueness of the Levi-Civita connection.
-/

@[expose] public section

namespace CovariantDerivative

open scoped Manifold Topology
open Bundle ContDiff VectorField CovariantDerivative

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I (M := M)))

/-- A covariant derivative `cov` on `TM` is **compatible with the
Riemannian metric** if `v · ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩` for all
smooth vector fields `Y, Z` and every point/direction `(x, v)`. -/
def IsMetricCompatible : Prop :=
  ∀ (Y Z : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y ↦ ⟪Y y, Z y⟫) x v = ⟪cov Y x v, Z x⟫ + ⟪Y x, cov Z x v⟫

/-- The Koszul formula for a smooth torsion-free metric-compatible covariant derivative. -/
theorem koszul_formula
    [cov.ContMDiffCovariantDerivative ∞]
    (_htor : cov.torsion = 0) (_hmet : cov.IsMetricCompatible)
    (X Y Z : Π x : M, TangentSpace I x)
    (_hX : CMDiff ∞ (T% X)) (_hY : CMDiff ∞ (T% Y)) (_hZ : CMDiff ∞ (T% Z))
    (x : M) :
    2 * ⟪cov Y x (X x), Z x⟫ =
      mvfderiv I (fun y ↦ ⟪Y y, Z y⟫) x (X x)
      + mvfderiv I (fun y ↦ ⟪X y, Z y⟫) x (Y x)
      - mvfderiv I (fun y ↦ ⟪X y, Y y⟫) x (Z x)
      - ⟪X x, mlieBracket I Y Z x⟫
      - ⟪Y x, mlieBracket I X Z x⟫
      + ⟪Z x, mlieBracket I X Y x⟫ := by
  have hXat : MDiffAt (T% X) x := _hX.contMDiffAt.mdifferentiableAt (by tauto)
  have hYat : MDiffAt (T% Y) x := _hY.contMDiffAt.mdifferentiableAt (by tauto)
  have hZat : MDiffAt (T% Z) x := _hZ.contMDiffAt.mdifferentiableAt (by tauto)
  have h_tor : ∀ {X' Y' : Π x : M, TangentSpace I x}, MDiffAt (T% X') x → MDiffAt (T% Y') x →
      cov Y' x (X' x) - cov X' x (Y' x) = mlieBracket I X' Y' x :=
    cov.torsion_eq_zero_iff.1 _htor
  rw [_hmet Y Z _hY _hZ .., _hmet X Z _hX _hZ .., _hmet X Y _hX _hY ..,
    ← h_tor hYat hZat, ← h_tor hXat hZat, ← h_tor hXat hYat, inner_sub_right, inner_sub_right,
    inner_sub_right, real_inner_comm (Z x), real_inner_comm (Z x), real_inner_comm (Y x)]
  ring

end CovariantDerivative

end
