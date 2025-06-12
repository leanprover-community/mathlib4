/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.GCongr.CoreAttrs

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`. In this file we set it up for use across the library by listing
`positivity` as a first-pass discharger for side goals (`gcongr_discharger`). -/

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)

/-!
We register `gcongr` with the `hint` tactic.
-/

register_hint gcongr

namespace Mathlib.Tactic.GCongr

/-!
Tag the relevant transitivity lemmas for `<` and `≤` with `@[gcongr]`.
The tags for `≤` aren't strictly necessary, but they help avoid an `IsTrans` type class search.
-/

variable {α : Type*}

section order

attribute [gcongr] lt_of_le_of_lt lt_of_le_of_lt' le_trans le_trans'

variable [Preorder α] {a b c d : α}

@[gcongr] theorem lt_imp_lt (h₁ : c ≤ a) (h₂ : b ≤ d) : a < b → c < d :=
  fun h => (h₁.trans_lt h).trans_le h₂

@[gcongr] theorem gt_imp_gt (h₁ : a ≤ c) (h₂ : d ≤ b) : a > b → c > d :=
  lt_imp_lt h₂ h₁

@[gcongr] theorem gt_imp_gt_left (hab : a ≤ b) : c > b → c > a := lt_of_le_of_lt hab

@[gcongr] theorem gt_imp_gt_right : b ≤ a → b > c → a > c := lt_of_le_of_lt'

/-- `le_imp_le` isn't strictly needed, but is a very common case, so still tag the lemma -/
@[gcongr] theorem le_imp_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a ≤ b → c ≤ d :=
  fun h => (h₁.trans h).trans h₂

end order

section subset

attribute [gcongr] ssubset_of_subset_of_ssubset

variable [HasSubset α] [HasSSubset α]  [IsNonstrictStrictOrder α (· ⊆ ·) (· ⊂ ·)]
  [IsTrans α (· ⊆ ·)] {a b c d : α}

@[gcongr]
theorem ssubset_imp_ssubset (h₁ : c ⊆ a) (h₂ : b ⊆ d) : a ⊂ b → c ⊂ d :=
  fun h => (h₁.trans_ssubset h).trans_subset h₂

@[gcongr]
theorem ssubset_imp_ssubset_right (h₁ : b ⊆ a) : c ⊂ b → c ⊂ a :=
  fun h₂ => (h₂.subset.trans h₁).ssubset_of_not_subset fun h => h₂.not_subset <| h₁.trans h

@[gcongr]
theorem ssuperset_imp_ssuperset (h₁ : a ⊆ c) (h₂ : d ⊆ b) : a ⊃ b → c ⊃ d :=
  ssubset_imp_ssubset h₂ h₁

@[gcongr]
theorem ssuperset_imp_ssuperset_right  (h : b ⊆ a) : b ⊃ c → a ⊃ c :=
  ssubset_imp_ssubset_right h

@[gcongr]
theorem ssuperset_imp_ssuperset_left  (h₁ : b ⊆ a) (h₂ : c ⊂ b) : c ⊂ a :=
  (h₂.subset.trans h₁).ssubset_of_not_subset fun h => h₂.not_subset <| h₁.trans h

end subset

end Mathlib.Tactic.GCongr
