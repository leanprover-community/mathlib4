/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Std.Tactic.ShowTerm

/-- `assumption?` is equivalent to `show_term assumption` -/
macro "assumption?" : tactic => `(tactic| show_term assumption)
