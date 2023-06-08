/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.LabelAttr

/-! # Stub attribute, for `is_poly`

This has to be in a separate file from `Mathlib.Tactic.LabelAttr`, and also a separate file
from the files that actually want to use the attribute, most likely the `WittVector` files.
-/

/-- A stub attribute for `is_poly`. -/
register_label_attr is_poly

/-- A stub attribute for `ghost_simps`. -/
register_label_attr ghost_simps
