/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Init

/-!
Mathlib-specific pretty printer options.
-/

open Lean

namespace Mathlib

/--
The `pp.mathlib.binderPredicates` option is used to control whether mathlib pretty printers
should use binder predicate notation (such as `∀ x < 2, p x`).
-/
register_option pp.mathlib.binderPredicates : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) pretty prints binders such as \
    `∀ (x : α) (x < 2), p x` as `∀ x < 2, p x`"
}

/-- Gets whether `pp.mathlib.binderPredicates` is enabled. -/
def getPPBinderPredicates (o : Options) : Bool :=
  o.get pp.mathlib.binderPredicates.name (!getPPAll o)

end Mathlib


/--
The `pp.mdata` option is used to control whether `Expr.mdata` nodes are pretty-printed.`
-/
register_option pp.mdata : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) pretty prints mdata annotations"
}

/-- Gets whether `Expr.mdata` delaboration is enabled. -/
def Lean.getPPMData (o : Options) : Bool :=
  o.get pp.mdata.name (getPPAll o)
