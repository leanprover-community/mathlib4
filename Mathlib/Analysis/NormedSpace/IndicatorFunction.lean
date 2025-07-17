/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.Pi
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Indicator function and (e)norm

This file contains a few simple lemmas about `Set.indicator`, `norm` and `enorm`.

## Tags
indicator, norm
-/

open Set

section ENormedAddMonoid

variable {α ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε] {s t : Set α} (f : α → ε) (a : α)

lemma enorm_indicator_eq_indicator_enorm :
    ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a :=
  flip congr_fun a (indicator_comp_of_zero (enorm_zero (E := ε))).symm

theorem enorm_indicator_le_of_subset (h : s ⊆ t) (f : α → ε) (a : α) :
    ‖indicator s f a‖ₑ ≤ ‖indicator t f a‖ₑ := by
  simp only [enorm_indicator_eq_indicator_enorm]
  apply indicator_le_indicator_of_subset ‹_› (zero_le _)

theorem indicator_enorm_le_enorm_self : indicator s (fun a => ‖f a‖ₑ) a ≤ ‖f a‖ₑ :=
  indicator_le_self' (fun _ _ ↦ zero_le _) a

theorem enorm_indicator_le_enorm_self : ‖indicator s f a‖ₑ ≤ ‖f a‖ₑ := by
  rw [enorm_indicator_eq_indicator_enorm]
  apply indicator_enorm_le_enorm_self

end ENormedAddMonoid

section SeminormedAddGroup

variable {α E : Type*} [SeminormedAddGroup E] {s t : Set α} (f : α → E) (a : α)

theorem norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm

theorem nnnorm_indicator_eq_indicator_nnnorm :
    ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm

theorem norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) :
    ‖indicator s f a‖ ≤ ‖indicator t f a‖ := by
  simp only [norm_indicator_eq_indicator_norm]
  exact indicator_le_indicator_of_subset ‹_› (fun _ => norm_nonneg _) _

theorem indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a ≤ ‖f a‖ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a

theorem norm_indicator_le_norm_self : ‖indicator s f a‖ ≤ ‖f a‖ := by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self

end SeminormedAddGroup
