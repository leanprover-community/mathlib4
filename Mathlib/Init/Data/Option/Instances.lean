/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Classes.LawfulMonad
import Std.Data.Option.Basic
import Mathlib.Mathport.Rename

/-!
# Port of Lean 3's `init/data/option/instances.lean`

The lawful monad instance for `Option` comes from `Std`.
The other theorems already exist in core or std.
-/

theorem Option.eq_some_of_isSome {α : Type _} : ∀ {o : Option α} (h : Option.isSome o = true), o = some (Option.get _ h)
  | some _, _ => rfl

#align option.eq_none_of_is_none Option.eq_none_of_isNone
#align option.eq_some_of_is_some Option.eq_some_of_isSome
