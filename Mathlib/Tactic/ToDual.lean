/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

import all Init.Core  -- TODO: for accessing proofs
public import Mathlib.Tactic.Translate.ToDual


/-!
## `@[to_dual]` attributes for basic types
-/

public meta section

attribute [to_dual self (reorder := 3 4)] LE.le LT.lt GE.ge GT.gt

/-
`DecidableLT` is defined as `∀ a b : α, Decidable (a < b)`, which is dual to
`∀ a b : α, Decidable (b < a)`. Translations given by `to_dual` need to satisfy the
property that if `e₁` is defEq to `e₂`, then the dual of `e₁` needs to be defEq to
the dual of `e₂`. Hence, the translation of `DecidableLT` needs to be defEq to
`∀ a b : α, Decidable (b < a)`. So, we define `DecidableLT'` to be this.

`DecidableLT'` is not definitionally the same as `DecidableLT`, but for type class search
the two are identical. So although this is a bit annoying, it is not a big problem.
-/
attribute [to_dual DecidableLT' /-- `DecidableLT'` is equivalent to `DecidableLT`.
It is used by `@[to_dual]` in order to deal with `DecidableLT`. -/] DecidableLT
attribute [to_dual DecidableLE' /-- `DecidableLE'` is equivalent to `DecidableLE`.
It is used by `@[to_dual]` in order to deal with `DecidableLE`. -/] DecidableLE

attribute [to_dual_do_translate] Empty PEmpty Unit PUnit
attribute [to_dual_ignore_args 2] Subtype

set_option linter.existingAttributeWarning false in
attribute [to_dual self] ge_iff_le gt_iff_lt

attribute [to_dual le_of_eq_of_le''] le_of_eq_of_le
attribute [to_dual le_of_le_of_eq''] le_of_le_of_eq
attribute [to_dual lt_of_eq_of_lt''] lt_of_eq_of_lt
attribute [to_dual lt_of_lt_of_eq''] lt_of_lt_of_eq

attribute [to_dual] Max

-- We need to tag the lemmas used by `grind` in order to translate `grind` proofs.
namespace Lean.Grind.Order

attribute [to_dual existing le_of_eq_1] le_of_eq_2
attribute [to_dual self] le_of_not_le lt_of_not_le le_of_not_lt
attribute [to_dual self (reorder := 6 7)] eq_of_le_of_le
attribute [to_dual self (reorder := a c, h₁ h₂)] le_trans lt_trans
attribute [to_dual existing (reorder := a c, h₁ h₂) le_lt_trans] lt_le_trans
attribute [to_dual self] le_eq_true_of_lt le_eq_false_of_lt lt_eq_false_of_lt lt_eq_false_of_le

/- For now, we don't tag any `grind` lemmas involving offsets, but this may be done in the future.
These offset lemmas are:

le_of_eq_1_k, le_of_eq_2_k, le_of_not_lt_k, lt_of_not_le_k, le_trans_k, lt_trans_k, le_lt_trans_k,
lt_le_trans_k, le_unsat_k, lt_unsat_k, le_eq_true_of_le_k, le_eq_true_of_lt_k, lt_eq_true_of_lt_k,
lt_eq_true_of_le_k, le_eq_false_of_le_k, lt_eq_false_of_le_k, lt_eq_false_of_lt_k,
le_eq_false_of_lt_k -/

end Lean.Grind.Order
