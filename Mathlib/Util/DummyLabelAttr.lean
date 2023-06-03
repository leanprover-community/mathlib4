/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.LabelAttr

/-! # Dummy label attribute, for tests

This has to be in a separate file from `Mathlib.Tactic.LabelAttr`, and also a separate file
from the files in `test/` that actually want to use it, so it ends up alone. This could be in
`test/` but the tests are set up for single file use only and can only import things from mathlib.
-/

/-- A dummy label attribute, to ease testing. -/
register_label_attr dummy_label_attr
