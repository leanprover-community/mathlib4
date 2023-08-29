/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.IndicatorFunction

#align_import analysis.normed_space.indicator_function from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# Indicator function and norm

This file contains a few simple lemmas about `Set.indicator` and `norm`.

## Tags
indicator, norm
-/


variable {α E : Type*} [SeminormedAddCommGroup E] {s t : Set α} (f : α → E) (a : α)

open Set

theorem norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm
#align norm_indicator_eq_indicator_norm norm_indicator_eq_indicator_norm

theorem nnnorm_indicator_eq_indicator_nnnorm :
    ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm
#align nnnorm_indicator_eq_indicator_nnnorm nnnorm_indicator_eq_indicator_nnnorm

theorem norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) :
    ‖indicator s f a‖ ≤ ‖indicator t f a‖ := by
  simp only [norm_indicator_eq_indicator_norm]
  -- ⊢ indicator s (fun a => ‖f a‖) a ≤ indicator t (fun a => ‖f a‖) a
  exact indicator_le_indicator_of_subset ‹_› (fun _ => norm_nonneg _) _
  -- 🎉 no goals
#align norm_indicator_le_of_subset norm_indicator_le_of_subset

theorem indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a ≤ ‖f a‖ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a
#align indicator_norm_le_norm_self indicator_norm_le_norm_self

theorem norm_indicator_le_norm_self : ‖indicator s f a‖ ≤ ‖f a‖ := by
  rw [norm_indicator_eq_indicator_norm]
  -- ⊢ indicator s (fun a => ‖f a‖) a ≤ ‖f a‖
  apply indicator_norm_le_norm_self
  -- 🎉 no goals
#align norm_indicator_le_norm_self norm_indicator_le_norm_self
