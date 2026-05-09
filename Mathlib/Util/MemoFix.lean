/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Edward Ayers
-/
module

public import Std.Data.HashMap.Basic
public import Mathlib.Init

/-!
# Fixpoint function with memoisation

-/

variable {α β : Type}

@[noinline, deprecated "deprecated without replacement" (since := "2026-01-24")]
def injectIntoBaseIO {α : Type} (a : α) : BaseIO α := pure a

set_option linter.deprecated false in
@[deprecated "deprecated without replacement" (since := "2026-01-24")]
unsafe def memoFixImpl [Nonempty β] (f : (α → β) → (α → β)) : α → β := unsafeBaseIO do
  let cache : IO.Ref (Lean.PtrMap α β) ← ST.mkRef Lean.mkPtrMap
  let rec fix (a) : β := unsafeBaseIO do
    if let some b := (← cache.get).find? a then
      return b
    let b ← injectIntoBaseIO (f fix a)
    cache.modify (·.insert a b)
    return b
  return fix

/-- Takes the fixpoint of `f` with caching of values that have been seen before.
Hashing makes use of a pointer hash.

This is useful for implementing tree traversal functions where
subtrees may be referenced in multiple places.
-/
@[implemented_by memoFixImpl,
deprecated "use `MonadCacheT`  and `checkCache`" (since := "2026-01-24")]
public opaque memoFix [Nonempty β] (f : (α → β) → (α → β)) : α → β
