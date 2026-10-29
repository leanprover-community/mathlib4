/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Lean.Elab.InfoTree.Util
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Linting against defeq abuse

This file adds a linter agains uses of `⟨...⟩` notation that introduce defeq abuse.
This is particularly common when using a definition, such as `def NNReal := {r : ℝ | 0 ≤ r}`.
Instead, we should define a specialized constructor `NNReal.mk : (r : ℝ) → 0 ≤ r → NNReal`.
-/

public meta section

open Lean Meta Elab

namespace Mathlib.Linter

/--
The defeqAbuse linter flags uses of the anonymous constructor notation `⟨...⟩`
that rely on defeq abuse.
-/
register_option linter.defeqAbuse : Bool := {
  defValue := false
  descr := "lint agains defeq abuse"
}

/-- Lints against using constructors with internal names during elaboration. -/
def defeqAbuse : Linter where
  run := withSetOptionIn fun _ => do
    unless Linter.getLinterValue linter.defeqAbuse (← Linter.getLinterOptions) do
      return
    let env ← getEnv
    -- Collect the warnings separately from logging them, since (compiled) `foldInfo` is faster
    -- than (interpreted, specialized) `foldInfoM`.
    let arr := (← getInfoTrees).foldl (init := #[]) <|
      InfoTree.foldInfo fun ctx info arr => Id.run do
      let .ofTermInfo i := info | return arr
      if i.elaborator != `Lean.Elab.Term.elabAnonymousCtor then return arr
      let some expectedTy := i.expectedType? | return arr
      let .const ctor _ := i.expr.getAppFn | return arr
      let some (.ctorInfo { induct, type, .. }) := env.find? ctor | return arr
      -- This check is for performance. We later do the stronger check on `← whnfI expectedTy`.
      if expectedTy.isConstOf induct then return arr
      -- Do not lint on propositions
      if (env.find? induct).get!.type.getForallBody.isProp then return arr
      return arr.push (ctx, induct, expectedTy, i)
    for (ctx, induct, expectedTy, i) in arr do
      Command.liftCoreM do MetaM.run' do withLCtx i.lctx {} do withMCtx ctx.mctx do
      if !(← whnfI expectedTy).isConstOf induct then
        Linter.logLint linter.defeqAbuse i.stx
          m!"The expected type `{expectedTy}` is different from the structure \
          `{.ofConstName induct}` at implicit transparency.\n\
          Such defeq abuse should be avoided as it can cause unification problems.\n\
          Instead, consider using a specialized version of `{i.expr.getAppFn.constName!}`."

initialize addLinter defeqAbuse

end Mathlib.Linter
