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

private unsafe def memoFixImplObj (f : (Object → Object) → (Object → Object)) (a : Object) : Object := unsafeBaseIO do
  let cache : IO.Ref ObjectMap ← ST.mkRef (mkObjectMap ())
  let rec fix (a) := unsafeBaseIO do
    if let some b := (← cache.get).find? a then
      return b
    let b := f fix a
    cache.modify (·.insert a b)
    pure b
  pure $ fix a

private unsafe def memoFixImpl {α : Type u} {β : Type v} [Nonempty β] : (f : (α → β) → (α → β)) → (a : α) → β :=
  unsafeCast memoFixImplObj

/-- Takes the fixpoint of `f` with caching of values that have been seen before.
Hashing makes use of a pointer hash.

This is useful for implementing tree traversal functions where
subtrees may be referenced in multiple places.
-/
@[implementedBy memoFixImpl]
constant memoFix {α : Type u} {β : Type v} [Nonempty β] (f : (α → β) → (α → β)) : α → β
