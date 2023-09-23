/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Tactic.LabelAttr

/-! # Stub attributes for `is_poly` and `ghost_simps`

This has to be in a separate file from `Mathlib.Tactic.LabelAttr`, and also a separate file
from the files that actually use the attribute, most likely the `WittVector` files.
-/

/-- A stub attribute for `is_poly`. -/
register_label_attr is_poly

/-- Simplification rules for ghost equations. -/
register_simp_attr ghost_simps
