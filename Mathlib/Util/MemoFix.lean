/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Edward Ayers
-/
import Std.Data.HashMap.Basic
import Mathlib.Init

/-!
# Fixpoint function with memoisation

-/

universe u v
open ShareCommon Std

private unsafe abbrev ObjectMap := @Std.HashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.hash⟩

@[noinline]
private def injectIntoBaseIO {α : Type} (a : α) : BaseIO α := pure a

private unsafe def memoFixImplObj (f : (Object → Object) → (Object → Object)) (a : Object) :
    Object := unsafeBaseIO do
  let cache : IO.Ref ObjectMap ← ST.mkRef ∅
  let rec fix (a) := unsafeBaseIO do
    if let some b := (← cache.get)[a]? then
      return b
    let b ← injectIntoBaseIO (f fix a)
    cache.modify (·.insert a b)
    pure b
  pure <| fix a

private unsafe def memoFixImpl {α : Type u} {β : Type v} [Nonempty β] :
    (f : (α → β) → (α → β)) → (a : α) → β :=
  unsafeCast memoFixImplObj

/-- Takes the fixpoint of `f` with caching of values that have been seen before.
Hashing makes use of a pointer hash.

This is useful for implementing tree traversal functions where
subtrees may be referenced in multiple places.
-/
@[implemented_by memoFixImpl]
opaque memoFix {α : Type u} {β : Type v} [Nonempty β] (f : (α → β) → (α → β)) : α → β
