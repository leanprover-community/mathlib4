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

/-- Which trace classes are exempted from the `unregisteredTraceClass` linter. If unnecessary, a
warning is logged on the exempted `Ident`. -/
public meta initialize allowedUnregisteredTraceClasses : EnvExtension (List Ident) ←
  registerEnvExtension (pure [])

/-- Allows exempting a specific trace class from the `unregisteredTraceClass` linter, meaning that
`cls` can be used in `trace[cls]` in the current file (above or below this command) without being
registered in this file. This does not persist across files. -/
elab "allow_unregistered_trace_class " cls:ident : command =>
  modifyEnv fun env => allowedUnregisteredTraceClasses.modifyState env (cls :: ·)

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
    let localAllowed := allowedUnregisteredTraceClasses.getState (← getEnv)
    unless localAllowed.isEmpty do
      for exemptCls in localAllowed do
        if optionDecls.contains exemptCls.getId then
          logWarningAt exemptCls m!"The trace class `{exemptCls.getId}` is already registered in \
            an imported file." -- TODO: show which
        else unless traceClasses.contains exemptCls.getId do
          logWarningAt exemptCls m!"The trace class `{exemptCls.getId}` is not used in this file."
      traceClasses := traceClasses.filter fun cls _ => localAllowed.all (·.getId != cls)
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
      for exemptCls in localAllowed do
        if inits.contains exemptCls.getId then
          logWarningAt exemptCls m!"The trace class `{exemptCls.getId}` is registered in this file."
          -- TODO: show where
      for (cls, refs) in traceClasses do
        if inits.contains cls then continue
        for ref in refs do
          logWarningAt ref m!"The trace class `{cls}` is not already registered, nor is it \
            obviously registered later in this file. Use\
            {indentD m!"initialize {.ofConstName ``registerTraceClass} `{cls}"}\n\
            to make the trace class available via `set_option trace.{cls}` in subsequent files.\n\n\
            Or, use `allow_unregistered_trace_class <cls>` at some point in this file to exempt \
            the class.\n\n\
            Use `set_option linter.unregisteredTraceClass false` to disable this linter entirely."

meta unsafe initialize addModuleLinter unregisteredTraceClass

end Mathlib.Linter
