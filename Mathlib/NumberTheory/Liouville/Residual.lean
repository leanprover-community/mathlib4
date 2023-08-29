/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.NumberTheory.Liouville.Basic
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Topology.Instances.Irrational

#align_import number_theory.liouville.residual from "leanprover-community/mathlib"@"32b08ef840dd25ca2e47e035c5da03ce16d2dc3c"

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/


open scoped Filter

open Filter Set Metric

theorem setOf_liouville_eq_iInter_iUnion :
    { x | Liouville x } =
      ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b),
      ball ((a : ℝ) / b) (1 / (b : ℝ) ^ n) \ {(a : ℝ) / b} := by
  ext x
  -- ⊢ x ∈ {x | Liouville x} ↔ x ∈ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball ( …
  simp only [mem_iInter, mem_iUnion, Liouville, mem_setOf_eq, exists_prop, mem_diff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm]
#align set_of_liouville_eq_Inter_Union setOf_liouville_eq_iInter_iUnion

theorem isGδ_setOf_liouville : IsGδ { x | Liouville x } := by
  rw [setOf_liouville_eq_iInter_iUnion]
  -- ⊢ IsGδ (⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b) (1 / ↑b ^ n)  …
  refine isGδ_iInter fun n => IsOpen.isGδ ?_
  -- ⊢ IsOpen (⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b) (1 / ↑b ^ n) \ {↑a / ↑ …
  refine isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => ?_
  -- ⊢ IsOpen (ball (↑a / ↑b) (1 / ↑b ^ n) \ {↑a / ↑b})
  exact isOpen_ball.inter isClosed_singleton.isOpen_compl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_Gδ_set_of_liouville isGδ_setOf_liouville

theorem setOf_liouville_eq_irrational_inter_iInter_iUnion :
    { x | Liouville x } =
      { x | Irrational x } ∩ ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (hb : 1 < b),
      ball (a / b) (1 / (b : ℝ) ^ n) := by
  refine Subset.antisymm ?_ ?_
  -- ⊢ {x | Liouville x} ⊆ {x | Irrational x} ∩ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 …
  · refine subset_inter (fun x hx => hx.irrational) ?_
    -- ⊢ {x | Liouville x} ⊆ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b) …
    rw [setOf_liouville_eq_iInter_iUnion]
    -- ⊢ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b) (1 / ↑b ^ n) \ {↑a  …
    exact iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun _hb => diff_subset _ _
    -- 🎉 no goals
  · simp only [inter_iInter, inter_iUnion, setOf_liouville_eq_iInter_iUnion]
    -- ⊢ ⋂ (i : ℕ), ⋃ (i_1 : ℤ) (i_2 : ℤ) (_ : 1 < i_2), {x | Irrational x} ∩ ball (↑ …
    refine iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun hb => ?_
    -- ⊢ {x | Irrational x} ∩ ball (↑a / ↑b) (1 / ↑b ^ n) ⊆ ball (↑a / ↑b) (1 / ↑b ^  …
    rw [inter_comm]
    -- ⊢ ball (↑a / ↑b) (1 / ↑b ^ n) ∩ {x | Irrational x} ⊆ ball (↑a / ↑b) (1 / ↑b ^  …
    exact diff_subset_diff Subset.rfl (singleton_subset_iff.2 ⟨a / b, by norm_cast⟩)
    -- 🎉 no goals
#align set_of_liouville_eq_irrational_inter_Inter_Union setOf_liouville_eq_irrational_inter_iInter_iUnion

/-- The set of Liouville numbers is a residual set. -/
theorem eventually_residual_liouville : ∀ᶠ x in residual ℝ, Liouville x := by
  rw [Filter.Eventually, setOf_liouville_eq_irrational_inter_iInter_iUnion]
  -- ⊢ {x | Irrational x} ∩ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b …
  refine eventually_residual_irrational.and ?_
  -- ⊢ ∀ᶠ (x : ℝ) in residual ℝ, x ∈ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball …
  refine eventually_residual.2 ⟨_, ?_, Rat.denseEmbedding_coe_real.dense.mono ?_, Subset.rfl⟩
  -- ⊢ IsGδ (⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b) (1 / ↑b ^ n))
  · exact isGδ_iInter fun n => IsOpen.isGδ <|
          isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => isOpen_ball
  · rintro _ ⟨r, rfl⟩
    -- ⊢ ↑r ∈ ⋂ (n : ℕ), ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b), ball (↑a / ↑b) (1 / ↑b ^ n)
    simp only [mem_iInter, mem_iUnion]
    -- ⊢ ∀ (i : ℕ), ∃ i_1 i_2 i_3, ↑r ∈ ball (↑i_1 / ↑i_2) (1 / ↑i_2 ^ i)
    refine fun n => ⟨r.num * 2, r.den * 2, ?_, ?_⟩
    -- ⊢ 1 < ↑r.den * 2
    · have := Int.ofNat_le.2 r.pos; rw [Int.ofNat_one] at this; linarith
      -- ⊢ 1 < ↑r.den * 2
                                    -- ⊢ 1 < ↑r.den * 2
                                                                -- 🎉 no goals
    · convert @mem_ball_self ℝ _ (r : ℝ) _ _
      -- ⊢ ↑(r.num * 2) / ↑(↑r.den * 2) = ↑r
      · push_cast; norm_cast; simp [Rat.divInt_mul_right (two_ne_zero), Rat.mkRat_self]
        -- ⊢ ↑r.num * 2 / (↑r.den * 2) = ↑r
                   -- ⊢ Rat.divInt (r.num * 2) ↑(r.den * 2) = r
                              -- 🎉 no goals
      · refine' one_div_pos.2 (pow_pos (Int.cast_pos.2 _) _)
        -- ⊢ 0 < ↑r.den * 2
        exact mul_pos (Int.coe_nat_pos.2 r.pos) zero_lt_two
        -- 🎉 no goals
#align eventually_residual_liouville eventually_residual_liouville

/-- The set of Liouville numbers in dense. -/
theorem dense_liouville : Dense { x | Liouville x } :=
    dense_of_mem_residual eventually_residual_liouville
#align dense_liouville dense_liouville
