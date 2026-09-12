/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Tactic.FunSimp.Attr

/-!
# Simprocs for rewriting prefixes of applications

These simprocs try to rewrite every prefix of an application. This is necessary because
`@[fun_simp]` normalizes equalities into an unapplied form, e.g. `f (x + 1) y = x + y` becomes
`f (x + 1) = fun y => x + y`.
-/

open Lean Meta.Simp

public meta section

namespace Mathlib.Tactic.FunSimp

/-- Post-rewriting partial applications in `fun_simp`. -/
simproc_decl partialAppPost (_) := fun e => do
  let rec go (e : Expr) := do
    let .app f x := e | return none
    if let some r ← go f then
      return some (← mkCongrFun r x)
    let thms ← simpExt.getTheorems
    rewrite? e thms.post thms.erased "fun_simp post" false
  if let some res ← go e then
    return .visit res
  return .continue

/-- Pre-rewriting partial applications in `fun_simp`. -/
simproc_decl partialAppPre (_) := fun e => do
  let rec go (e : Expr) := do
    let .app f x := e | return none
    let thms ← simpExt.getTheorems
    if let some r ← rewrite? e thms.pre thms.erased "fun_simp pre" false then
      return some r
    (← go f).mapM (mkCongrFun · x)
  if let some res ← go e then
    return .visit res
  return .continue

attribute [fun_simp_proc↓] partialAppPre
attribute [fun_simp_proc↑] partialAppPost

end Mathlib.Tactic.FunSimp
