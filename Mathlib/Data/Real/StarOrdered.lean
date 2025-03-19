/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Real.Sqrt

/-! # `ℝ` and `ℝ≥0` are *-ordered rings. -/

open scoped NNReal

/-- Although the instance `RCLike.toStarOrderedRing` exists, it is locked behind the
`ComplexOrder` scope because currently the order on `ℂ` is not enabled globally. But we
want `StarOrderedRing ℝ` to be available globally, so we include this instance separately.
In addition, providing this instance here makes it available earlier in the import
hierarchy; otherwise in order to access it we would need to import `Mathlib.Analysis.RCLike.Basic`.
-/
instance Real.instStarOrderedRing : StarOrderedRing ℝ :=
  StarOrderedRing.of_nonneg_iff' add_le_add_left fun r => by
    refine ⟨fun hr => ⟨√r, (mul_self_sqrt hr).symm⟩, ?_⟩
    rintro ⟨s, rfl⟩
    exact mul_self_nonneg s

instance NNReal.instStarOrderedRing : StarOrderedRing ℝ≥0 := by
  refine .of_le_iff fun x y ↦ ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    refine ⟨sqrt d, ?_⟩
    simp only [star_trivial, mul_self_sqrt]
  · rintro ⟨p, -, rfl⟩
    exact le_self_add

lemma Real.exists_nat_pos_inv_lt {b : ℝ} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ)⁻¹ < b := by
  refine (exists_nat_gt b⁻¹).imp fun k hk ↦ ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

lemma NNReal.exists_nat_pos_inv_lt {b : ℝ≥0} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ≥0)⁻¹ < b :=
  b.toReal.exists_nat_pos_inv_lt hb
