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

attribute [gcongr] lt_of_le_of_lt lt_of_le_of_lt' le_trans le_trans'

variable {α : Type} [Preorder α]

@[gcongr]
theorem lt_imp_lt {a b c d : α} (h₁ : c ≤ a) (h₂ : b ≤ d) : a < b → c < d :=
  fun h => (h₁.trans_lt h).trans_le h₂

@[gcongr]
theorem le_imp_le {a b c d : α} (h₁ : c ≤ a) (h₂ : b ≤ d) : a ≤ b → c ≤ d :=
  fun h => (h₁.trans h).trans h₂

end Mathlib.Tactic.GCongr
