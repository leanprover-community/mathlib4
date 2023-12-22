/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.MLList.Basic

/-!
# Basic operations on `MLList`

These functions can be upstreamed to Std when convenient.
-/

set_option autoImplicit true

namespace MLList

/-- Construct a singleton monadic lazy list from a single monadic value. -/
def singletonM [Monad m] (x : m α) : MLList m α :=
  .squash fun _ => do return .cons (← x) .nil

/-- Construct a singleton monadic lazy list from a single value. -/
def singleton [Monad m] (x : α) : MLList m α :=
  .singletonM (pure x)

end MLList
