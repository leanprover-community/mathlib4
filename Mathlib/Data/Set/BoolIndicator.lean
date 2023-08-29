/-
Copyright (c) 2022 Dagur Tómas Ásgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Tómas Ásgeirsson, Leonardo de Moura
-/
import Mathlib.Data.Set.Image

#align_import data.set.bool_indicator from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Indicator function valued in bool

See also `Set.indicator` and `Set.piecewise`.
-/

open Bool

namespace Set

variable {α : Type*} (s : Set α)

/-- `boolIndicator` maps `x` to `true` if `x ∈ s`, else to `false` -/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x ∈ s) (Classical.propDecidable _) true false
#align set.bool_indicator Set.boolIndicator

theorem mem_iff_boolIndicator (x : α) : x ∈ s ↔ s.boolIndicator x = true := by
  unfold boolIndicator
  -- ⊢ x ∈ s ↔ (if x ∈ s then true else false) = true
  split_ifs with h <;> simp [h]
  -- ⊢ x ∈ s ↔ true = true
                       -- 🎉 no goals
                       -- 🎉 no goals
#align set.mem_iff_bool_indicator Set.mem_iff_boolIndicator

theorem not_mem_iff_boolIndicator (x : α) : x ∉ s ↔ s.boolIndicator x = false := by
  unfold boolIndicator
  -- ⊢ ¬x ∈ s ↔ (if x ∈ s then true else false) = false
  split_ifs with h <;> simp [h]
  -- ⊢ ¬x ∈ s ↔ False
                       -- 🎉 no goals
                       -- 🎉 no goals
#align set.not_mem_iff_bool_indicator Set.not_mem_iff_boolIndicator

theorem preimage_boolIndicator_true : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x ↦ (s.mem_iff_boolIndicator x).symm
#align set.preimage_bool_indicator_true Set.preimage_boolIndicator_true

theorem preimage_boolIndicator_false : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x ↦ (s.not_mem_iff_boolIndicator x).symm
#align set.preimage_bool_indicator_false Set.preimage_boolIndicator_false

open Classical

theorem preimage_boolIndicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if true ∈ t then s else ∅) ∪ if false ∈ t then sᶜ else ∅ := by
  ext x
  -- ⊢ x ∈ boolIndicator s ⁻¹' t ↔ x ∈ (if true ∈ t then s else ∅) ∪ if false ∈ t t …
  simp only [boolIndicator, mem_preimage]
  -- ⊢ (if x ∈ s then true else false) ∈ t ↔ x ∈ (if true ∈ t then s else ∅) ∪ if f …
  split_ifs <;> simp [*]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align set.preimage_bool_indicator_eq_union Set.preimage_boolIndicator_eq_union

theorem preimage_boolIndicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨
      s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ := by
  simp only [preimage_boolIndicator_eq_union]
  -- ⊢ ((if true ∈ t then s else ∅) ∪ if false ∈ t then sᶜ else ∅) = univ ∨ ((if tr …
  split_ifs <;> simp [s.union_compl_self]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align set.preimage_bool_indicator Set.preimage_boolIndicator

end Set
