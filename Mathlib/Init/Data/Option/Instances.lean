/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Data.Option.Basic
import Init.Control.Lawful

universe u v

theorem Option.eq_none_of_is_none {α : Type u} : ∀ {o : Option α}, o.isNone → o = none
  | none, _ => rfl
