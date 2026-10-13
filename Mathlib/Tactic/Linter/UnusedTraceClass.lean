/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Meta.Eval
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# Unused trace class linter

This linter ensures that for any instance of `trace[foo.bar]`, `foo.bar` is already registered or
is registered by the end of the file.

## Future work

Does not consider `withTraceNode` and variants.
-/

namespace Mathlib.Linter

open Lean Elab Command Linter

/-- Lints against `trace[<cls>]` invocations for which no such `cls` is registered by the
end of the file. -/
public meta register_option linter.unregisteredTraceClass : Bool := {
  defValue := false
  descr := "Lints against `trace[<cls>]` invocations for which no such `cls` is registered by the \
    end of the file"
}

/-- Lints against unused trace classes from `trace[cls]` syntax. -/
public meta unsafe def unregisteredTraceClass : ModuleLinter where
  run cmds := do
    unless getLinterValue linter.unregisteredTraceClass (← getLinterOptions) do
      return
    let mut traceClasses : NameMap (Array Ident) := {}
    let optionDecls ← getOptionDecls
    for cmd in cmds do
      unless ← cmd |> withSetOptionIn fun _ =>
        return getLinterValue linter.unregisteredTraceClass (← getLinterOptions)
      do
        continue
      -- Most syntax never uses `trace[_]`, so let's use a faster compiled loop first
      let any? := cmd.find? fun
        | `(doElem| trace[$a] $_)
        | `(term| Macro.trace[$a] $_) => !a.raw.isAnyAntiquot
        | _ => false
      if any?.isSome then
        for stx in cmd.topDown do
          match stx with
          | `(doElem| trace[$cls] $_)
          | `(term| Macro.trace[$cls] $_) =>
            if cls.raw.isAnyAntiquot then continue
            unless optionDecls.contains <| `trace ++ cls.getId do
              traceClasses := traceClasses.alter cls.getId fun refs? => refs?.getD #[] |>.push cls
          | _ => pure ()
    unless traceClasses.isEmpty do
      let env := (← getEnv).setExporting false
      let (inits, _) := regularInitAttr.ext.getState env
      let rec gatherRegisteredClasses (acc : List Expr) (e : Expr) : List Expr :=
        match_expr e with
        | Lean.registerTraceClass cls _ _ =>
          if cls.hasFVar || cls.hasLooseBVars then acc else
            cls :: acc
        | Bind.bind _ _ _ _ first second =>
          let acc := gatherRegisteredClasses acc first
          match second with
          | Expr.lam _ _ body _ => gatherRegisteredClasses acc body
          | _ => acc
        | _ => acc
      let inits := inits.foldl (init := []) fun acc decl => Id.run do
        let some cinfo := env.find? decl | return acc
        let some value := cinfo.value? (allowOpaque := true) | return acc
        gatherRegisteredClasses acc value
      let inits ← inits.mapM fun cls =>
        liftTermElabM <| Meta.evalExpr' Name ``Name cls (checkMeta := false)
      for (cls, refs) in traceClasses do
        if inits.contains cls then continue
        for ref in refs do
          logWarningAt ref m!"The trace class `{cls}` is not already registered, nor is it \
            obviously registered later in this file. Use\
            {indentD m!"initialize {.ofConstName ``registerTraceClass} `{cls}"}\n\
            to make the trace class available via `set_option trace.{cls}` in subsequent files.\n\n\
            Or, use `set_option linter.unregisteredTraceClass false in` in front of this commmand \
            to turn this linter off."

meta unsafe initialize addModuleLinter unregisteredTraceClass

end Mathlib.Linter
