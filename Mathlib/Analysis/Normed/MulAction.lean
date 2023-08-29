/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Analysis.Normed.Field.Basic

#align_import analysis.normed.mul_action from "leanprover-community/mathlib"@"bc91ed7093bf098d253401e69df601fc33dde156"

/-!
# Lemmas for `BoundedSMul` over normed additive groups

Lemmas which hold only in `NormedSpace α β` are provided in another file.

Notably we prove that `NonUnitalSeminormedRing`s have bounded actions by left- and right-
multiplication. This allows downstream files to write general results about `BoundedSMul`, and then
deduce `const_mul` and `mul_const` results as an immediate corollary.
-/


variable {α β : Type*}

section SeminormedAddGroup

variable [SeminormedAddGroup α] [SeminormedAddGroup β] [SMulZeroClass α β]

variable [BoundedSMul α β]

theorem norm_smul_le (r : α) (x : β) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ := by
  simpa [smul_zero] using dist_smul_pair r 0 x
  -- 🎉 no goals
#align norm_smul_le norm_smul_le

theorem nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ ≤ ‖r‖₊ * ‖x‖₊ :=
  norm_smul_le _ _
#align nnnorm_smul_le nnnorm_smul_le

theorem dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) ≤ ‖s‖ * dist x y := by
  simpa only [dist_eq_norm, sub_zero] using dist_smul_pair s x y
  -- 🎉 no goals
#align dist_smul_le dist_smul_le

theorem nndist_smul_le (s : α) (x y : β) : nndist (s • x) (s • y) ≤ ‖s‖₊ * nndist x y :=
  dist_smul_le s x y
#align nndist_smul_le nndist_smul_le

theorem lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ ((· • ·) s : β → β) :=
  lipschitzWith_iff_dist_le_mul.2 <| dist_smul_le _
#align lipschitz_with_smul lipschitzWith_smul

theorem edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) ≤ ‖s‖₊ • edist x y :=
  lipschitzWith_smul s x y
#align edist_smul_le edist_smul_le

end SeminormedAddGroup

/-- Left multiplication is bounded. -/
instance NonUnitalSeminormedRing.to_boundedSMul [NonUnitalSeminormedRing α] : BoundedSMul α α where
  dist_smul_pair' x y₁ y₂ := by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂)
                                -- 🎉 no goals
  dist_pair_smul' x₁ x₂ y := by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y
                                -- 🎉 no goals
#align non_unital_semi_normed_ring.to_has_bounded_smul NonUnitalSeminormedRing.to_boundedSMul

/-- Right multiplication is bounded. -/
instance NonUnitalSeminormedRing.to_has_bounded_op_smul [NonUnitalSeminormedRing α] :
    BoundedSMul αᵐᵒᵖ α where
  dist_smul_pair' x y₁ y₂ := by
    simpa [sub_mul, dist_eq_norm, mul_comm] using norm_mul_le (y₁ - y₂) x.unop
    -- 🎉 no goals
  dist_pair_smul' x₁ x₂ y := by
    simpa [mul_sub, dist_eq_norm, mul_comm] using norm_mul_le y (x₁ - x₂).unop
    -- 🎉 no goals
#align non_unital_semi_normed_ring.to_has_bounded_op_smul NonUnitalSeminormedRing.to_has_bounded_op_smul

section SeminormedRing

variable [SeminormedRing α] [SeminormedAddCommGroup β] [Module α β]

theorem BoundedSMul.of_norm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖ ≤ ‖r‖ * ‖x‖) :
    BoundedSMul α β :=
  { dist_smul_pair' := fun a b₁ b₂ => by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂)
                                         -- 🎉 no goals
    dist_pair_smul' := fun a₁ a₂ b => by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }
                                         -- 🎉 no goals
#align has_bounded_smul.of_norm_smul_le BoundedSMul.of_norm_smul_le

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing α] [SeminormedAddGroup β]

variable [MulActionWithZero α β] [BoundedSMul α β]

theorem norm_smul (r : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖ := by
  by_cases h : r = 0
  -- ⊢ ‖r • x‖ = ‖r‖ * ‖x‖
  · simp [h, zero_smul α x]
    -- 🎉 no goals
  · refine' le_antisymm (norm_smul_le r x) _
    -- ⊢ ‖r‖ * ‖x‖ ≤ ‖r • x‖
    calc
      ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖ := by rw [inv_smul_smul₀ h]
      _ ≤ ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) := by gcongr; apply norm_smul_le
      _ = ‖r • x‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul]
#align norm_smul norm_smul

theorem nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊ :=
  NNReal.eq <| norm_smul r x
#align nnnorm_smul nnnorm_smul

end NormedDivisionRing

section NormedDivisionRingModule

variable [NormedDivisionRing α] [SeminormedAddCommGroup β]

variable [Module α β] [BoundedSMul α β]

theorem dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * dist x y := by
  simp_rw [dist_eq_norm, (norm_smul s (x - y)).symm, smul_sub]
  -- 🎉 no goals
#align dist_smul₀ dist_smul₀

theorem nndist_smul₀ (s : α) (x y : β) : nndist (s • x) (s • y) = ‖s‖₊ * nndist x y :=
  NNReal.eq <| dist_smul₀ s x y
#align nndist_smul₀ nndist_smul₀

theorem edist_smul₀ (s : α) (x y : β) : edist (s • x) (s • y) = ‖s‖₊ • edist x y := by
  simp only [edist_nndist, nndist_smul₀, ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]
  -- 🎉 no goals
#align edist_smul₀ edist_smul₀

end NormedDivisionRingModule
