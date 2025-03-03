/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init

/-!
# Note about deprecated files

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

# Unbundled algebra classes

These classes were part of an incomplete refactor described
[here on the github Wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1).
However a subset of them are widely used in mathlib3,
and it has been tricky to clean this up as this file was in core Lean 3.
-/

set_option linter.deprecated false

universe u v

variable {α : Sort u}

@[deprecated "No deprecation message was provided." (since := "2024-09-11")]
class IsLeftCancel (α : Sort u) (op : α → α → α) : Prop where
  left_cancel : ∀ a b c, op a b = op a c → b = c

@[deprecated "No deprecation message was provided." (since := "2024-09-11")]
class IsRightCancel (α : Sort u) (op : α → α → α) : Prop where
  right_cancel : ∀ a b c, op a b = op c b → a = c
