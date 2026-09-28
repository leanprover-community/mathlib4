/-
Copyright (c) 2026 Radu Irbe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Radu Irbe
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Affine contractions

For a real scalar `c` and a point `b`, the map `x ↦ c • x + b` is Lipschitz with
constant `‖c‖₊`, hence a contraction whenever `‖c‖₊ < 1`. On a complete space it
has a unique fixed point, namely `(1 - c)⁻¹ • b`. This packages the affine model
behind fixed-point iteration and value iteration on top of the existing
`LipschitzWith` and `ContractingWith` API.

## Main statements

* `lipschitzWith_smul_add`: `x ↦ c • x + b` is Lipschitz with constant `‖c‖₊`.
* `contractingWith_smul_add`: it is a contraction when `‖c‖₊ < 1`.
* `smul_add_fixedPoint_eq`: its fixed point is `(1 - c)⁻¹ • b`.
* `exists_unique_fixedPoint_smul_add`: over a complete nonempty space, it is unique.

## Tags

affine contraction, fixed point, Banach fixed-point theorem
-/

@[expose] public section

section AffineContraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The map `x ↦ c • x + b` is Lipschitz with constant `‖c‖₊`. -/
theorem lipschitzWith_smul_add (c : ℝ) (b : E) :
    LipschitzWith ‖c‖₊ (fun x ↦ c • x + b) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← smul_sub, norm_smul]
  exact le_rfl

/-- An affine map with `‖c‖₊ < 1` is a contraction with rate `‖c‖₊`. -/
theorem contractingWith_smul_add (c : ℝ) (hc : ‖c‖₊ < 1) (b : E) :
    ContractingWith ‖c‖₊ (fun x ↦ c • x + b) :=
  ⟨hc, lipschitzWith_smul_add c b⟩

/-- The fixed point of `x ↦ c • x + b` is `(1 - c)⁻¹ • b`, in the `ℝ`-module sense. -/
theorem smul_add_fixedPoint_eq (c : ℝ) (hc1 : c ≠ 1) (b : E) :
    c • ((1 - c)⁻¹ • b) + b = (1 - c)⁻¹ • b := by
  have h : c * (1 - c)⁻¹ + 1 = (1 - c)⁻¹ := by
    have h' : (1 - c : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
    field_simp
    ring
  rw [← smul_assoc, smul_eq_mul]
  nth_rewrite 2 [← one_smul ℝ b]
  rw [← add_smul, h]

/-- An affine contraction over a complete space has a unique fixed point. -/
theorem exists_unique_fixedPoint_smul_add (c : ℝ) (hc : ‖c‖₊ < 1) (b : E)
    [Nonempty E] [CompleteSpace E] :
    ∃! x : E, c • x + b = x := by
  have hf := contractingWith_smul_add c hc b
  exact ⟨hf.fixedPoint, hf.fixedPoint_isFixedPt.eq, fun y hy ↦
    hf.fixedPoint_unique' hy hf.fixedPoint_isFixedPt⟩

end AffineContraction
