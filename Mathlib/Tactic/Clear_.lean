import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
syntax (name := clear_) "clear_" : tactic

/-- Is this name `Name.anonymous`? -/
def isAnonymous : Name → Bool
  | Name.anonymous => true
  | _ => false

/-- Does this name start with `_`? -/
def startsWithUnderscore : Name → Bool
  | Name.anonymous => false
  | Name.str pre str =>
    let first_char_is_underscore :=
      match str.data with
      | [] => false
      | x :: _ => x == '_'
    startsWithUnderscore pre || (isAnonymous pre && first_char_is_underscore)
  | Name.num pre _ => startsWithUnderscore pre

/-- Sort local declarations using an order `x < y` iff `x` was defined before `y`.-/
def sortLocalDeclOpts (lctx : LocalContext) (ldecls : Array (Option LocalDecl)) : Array (Option LocalDecl) :=
  ldecls.qsort fun ldecl_opt1 ldecl_opt2 =>
    match ldecl_opt1, ldecl_opt2 with
    | some ldecl1, some ldecl2 =>
      match lctx.find? ldecl1.fvarId, lctx.find? ldecl2.fvarId with
      | some d1, some d2 => d1.index < d2.index
      | some _, none => false
      | none, some _ => true
      | none, none => Name.quickLt ldecl1.fvarId.name ldecl2.fvarId.name
    | some _, none => false
    | none, some _ => true
    | none, none => false

elab_rules : tactic
  | `(tactic| clear_) => withMainContext do
    let mut lctx ← getLCtx
    let decl_opts := sortLocalDeclOpts lctx lctx.decls.toArray
    for decl_opt in decl_opts.reverse do
      match decl_opt with
      | some decl => do
        if(startsWithUnderscore decl.userName) then
          let fvarId := decl.fvarId
          let add_iff_dependent (ldecl : LocalDecl) (ldecls : List LocalDecl) :
            TacticM (List LocalDecl) := do
            if (ldecl.fvarId != fvarId && (← localDeclDependsOn ldecl fvarId)) then
              return ldecl :: ldecls
            else
              return ldecls
          let dependencies ← lctx.foldrM add_iff_dependent []
          let goal_decl ← getMVarDecl (← getMainGoal)
          if dependencies.isEmpty && not (← exprDependsOn goal_decl.type fvarId) then
            lctx := lctx.erase fvarId
            let mvarId ← clear (← getMainGoal) fvarId
            replaceMainGoal [mvarId]
      | none => continue
