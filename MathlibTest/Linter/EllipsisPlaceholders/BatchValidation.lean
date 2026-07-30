import Mathlib.Tactic.Linter.EllipsisPlaceholders

set_option linter.style.ellipsisPlaceholders true
set_option linter.unusedVariables false
-- Unit tests use a lower threshold than the default (`4`).
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2

def batchFn (a b c d : Nat) : Nat := a

-- Batch validation: apply every linter rewrite in this command and re-elaborate.
#guard_ellipsis_rewrites
#check batchFn 1 _ _

def instBatch {α : Type u} {β : Type v} [Add α] [Add β] (f : α → β) : Nat := 0

-- `@`-explicit: no rewrites collected.
#guard_ellipsis_rewrites
#check @instBatch _ _ _ _

def sixArg (a b c d e f : Nat) : Nat := a

#guard_ellipsis_rewrites
#check sixArg _ _ _ _ _ _
