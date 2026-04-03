/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!

This file gives theorems about Bool that could be upstreamed.

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

-/

@[expose] public section

namespace Bool

theorem cond_apply {α β} (f g : α → β) {b : Bool} {a : α} :
    (bif b then f else g) a = bif b then f a else g a := by cases b <;> rfl

end Bool
