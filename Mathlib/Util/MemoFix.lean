/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, E.W.Ayers
-/
import Std

open Std ShareCommon

/-!
# Fixpoint function with memoisation

-/

private unsafe def memoFixImpl {α β : Type} [Inhabited β] (f : (α → β) → (α → β)) (a : α) : β := unsafeBaseIO do
  let cache : IO.Ref (@HashMap Object β ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩) ← ST.mkRef {}
  let rec fix (a : α) : β := unsafeBaseIO do
    if let some b := (← cache.get).find? (unsafeCast a) then
      return b
    let b := f fix a
    cache.modify (·.insert (unsafeCast a) b)
    pure b
  pure $ fix a

/-- Takes the fixpoint of `f` with caching of values that have been seen before.
Hashing makes use of a pointer hash.

This is useful for implementing tree traversal functions where
subtrees may be referenced in multiple places.
-/
@[implementedBy memoFixImpl]
constant memoFix {α β : Type} [Inhabited β] (f : (α → β) → (α → β)) : α → β
