/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Std.Data.HashMap.AdditionalOperations
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module (since := "2025-08-18")

/-!
# Convenience functions for hash maps

This is now reimplemented in the Lean standard library.
-/

namespace Std.HashMap

variable {α β γ : Type _} [BEq α] [Hashable α]

end Std.HashMap
