/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Module.Defs

/-!
# Ordered algebras

This file proves properties of algebras where both rings are ordered compatibly.

### TODO

`positivity` extension for `algebraMap`
-/

variable {α β : Type*} [OrderedCommSemiring α]

section OrderedSemiring
variable (β)
variable [OrderedSemiring β] [Algebra α β] [SMulPosMono α β] {a : α}

@[mono] lemma algebraMap_mono : Monotone (algebraMap α β) :=
  fun a₁ a₂ ha ↦ by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_le_smul_of_nonneg_right ha zero_le_one

/-- A version of `algebraMap_mono` for use by `gcongr` since it currently does not preprocess
`Monotone` conclusions. -/
@[gcongr] protected lemma GCongr.algebraMap_le_algebraMap {a₁ a₂ : α} (ha : a₁ ≤ a₂) :
    algebraMap α β a₁ ≤ algebraMap α β a₂ := algebraMap_mono _ ha

lemma algebraMap_nonneg (ha : 0 ≤ a) : 0 ≤ algebraMap α β a := by simpa using algebraMap_mono β ha

end OrderedSemiring

section StrictOrderedSemiring
variable [StrictOrderedSemiring β] [Algebra α β]

section SMulPosMono
variable [SMulPosMono α β] [SMulPosReflectLE α β] {a₁ a₂ : α}

@[simp] lemma algebraMap_le_algebraMap : algebraMap α β a₁ ≤ algebraMap α β a₂ ↔ a₁ ≤ a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

end SMulPosMono

section SMulPosStrictMono
variable [SMulPosStrictMono α β] {a a₁ a₂ : α}
variable (β)

@[mono] lemma algebraMap_strictMono : StrictMono (algebraMap α β) :=
  fun a₁ a₂ ha ↦ by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_lt_smul_of_pos_right ha zero_lt_one

/-- A version of `algebraMap_strictMono` for use by `gcongr` since it currently does not preprocess
`Monotone` conclusions. -/
@[gcongr] protected lemma GCongr.algebraMap_lt_algebraMap {a₁ a₂ : α} (ha : a₁ < a₂) :
    algebraMap α β a₁ < algebraMap α β a₂ := algebraMap_strictMono _ ha

lemma algebraMap_pos (ha : 0 < a) : 0 < algebraMap α β a := by
  simpa using algebraMap_strictMono β ha

variable {β}
variable [SMulPosReflectLT α β]

@[simp] lemma algebraMap_lt_algebraMap : algebraMap α β a₁ < algebraMap α β a₂ ↔ a₁ < a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

end SMulPosStrictMono
end StrictOrderedSemiring
