/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.DefEqTransformations
public import Mathlib.Tactic.FunProp

/-!
# The `fun_prop_simp` tactic
-/

namespace Mathlib.Tactic

open Lean Elab Meta Tactic Syntax
open Mathlib.Meta.FunProp (getFunPropDecl?)

/-- `fun_prop_simp` is a wrapper around `fun_prop` that also tries calling `simp` on the function.
It is intended to be used as an `autoParam` for proving properties of bundled morphisms. -/
elab (name := funPropSimp) "fun_prop_simp" : tactic => do
  let goalType ← whnfR (← (← getMainGoal).getType)
  let some funPropDecl ← getFunPropDecl? goalType | throwError "Not a `fun_prop` goal"
  evalTactic <| ← `(tactic|
    first
    | fun_prop
    | conv =>
        arg @$(mkNatLit (funPropDecl.funArgId + 1))
        with_reducible eta_expand
        simp
      fun_prop
    | fail "`fun_prop_simp` failed"
  )

end Mathlib.Tactic
