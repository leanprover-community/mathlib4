/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
/-! # Register the `pp.beta` option itself

Users should import `Mathlib.Util.PPBeta`.
This module is merely registering the `pp.beta` option,
which needs to be done in a separate module.
-/

namespace Lean

/-!
Note to the future: if https://github.com/leanprover/lean4/issues/715
is addressed, then there *should* be a name collision in this file.
In that eventuality, you may remove both this module and `Mathlib.Util.PPBeta`.
-/

/-- The `pp.beta` option enables a pretty printer that beta reduces all
expressions. -/
register_option pp.beta : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) apply beta-reduction when pretty printing"
}

end Lean
