/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Tactic.ToAdditive.ToDual


/-!
## `@[to_dual]` attributes for basic types
-/

attribute [to_dual self (reorder := 3 4)] LE.le LT.lt GE.ge GT.gt

attribute [to_dual DecidableGT "`DecidableGT` is equivalent to `DecidableLT`."] DecidableLT
attribute [to_dual DecidableGE "`DecidableGE` is equivalent to `DecidableLE`."] DecidableLE

set_option linter.existingAttributeWarning false in
attribute [to_dual self (reorder := 3 4)] ge_iff_le gt_iff_lt

attribute [to_dual le_of_eq_of_le''] le_of_eq_of_le
attribute [to_dual le_of_le_of_eq''] le_of_le_of_eq
attribute [to_dual lt_of_eq_of_lt''] lt_of_eq_of_lt
attribute [to_dual lt_of_lt_of_eq''] lt_of_lt_of_eq

attribute [to_dual] Max
