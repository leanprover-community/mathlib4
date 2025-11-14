/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Tactic.ToAdditive.ToDual


/-!
## `@[to_dual]` attributes for basic types
-/

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

set_option linter.existingAttributeWarning false in
attribute [to_dual self (reorder := 3 4)] ge_iff_le gt_iff_lt

attribute [to_dual le_of_eq_of_le''] le_of_eq_of_le
attribute [to_dual le_of_le_of_eq''] le_of_le_of_eq
attribute [to_dual lt_of_eq_of_lt''] lt_of_eq_of_lt
attribute [to_dual lt_of_lt_of_eq''] lt_of_lt_of_eq

attribute [to_dual] Max
