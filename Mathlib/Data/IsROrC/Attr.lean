/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Lean

/-!
# Declare an `isROrC_simps` simp attribute.

Has to be in a separate file from `Data.IsROrC.Basic`, since simp attributes cannot be used directly
in the file that declares them.
-/

/-- "Simp attribute for lemmas about `IsROrC`" -/
register_simp_attr isROrC_simps
