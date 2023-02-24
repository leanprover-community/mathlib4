/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

/-!
# Basic properties on Ord
-/

set_option linter.unusedVariables false in
/-- The comap/pullback of an `Ord` instance. We explicitly name the `Ord β` instance,
so that it can be specified using an named argument, if needed. -/
def _root_.Ord.comap (f : α → β) [ord : Ord β] : Ord α where
  compare x y := compare (f x) (f y)
