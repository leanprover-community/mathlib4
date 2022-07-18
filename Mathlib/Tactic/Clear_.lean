import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

syntax (name := clear_) "clear_" : tactic

def isAnonymous : Name → Bool
  | Name.anonymous => true
  | _ => false

def startsWithUnderscore : Name → Bool
  | Name.anonymous => false
  | Name.str pre str =>
    let first_char_is_underscore :=
      match str.data with
      | [] => false
      | x :: _ => x == '_'
    startsWithUnderscore pre || (isAnonymous pre && first_char_is_underscore)
  | Name.num pre _ => startsWithUnderscore pre

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
elab_rules : tactic
  | `(tactic| clear_) => withMainContext do
    let mut lctx ← getLCtx
    let mut loopMadeChange := true -- Repeatedly loop until we are unable to remove anything else
    while loopMadeChange do
      loopMadeChange := false
      for decl_opt in lctx.decls do
        match decl_opt with
        | some decl => do
          if(startsWithUnderscore decl.userName) then
            let fvarId := decl.fvarId
            let add_iff_dependent (localDecl : LocalDecl) (localDecls : List LocalDecl) :
              TacticM (List LocalDecl) := do
              if (localDecl.fvarId != fvarId && (← localDeclDependsOn localDecl fvarId)) then
                return localDecl :: localDecls
              else
                return localDecls
            let dependencies ← lctx.foldrM add_iff_dependent []
            let goal_decl ← getMVarDecl (← getMainGoal)
            if dependencies.isEmpty && not (← exprDependsOn goal_decl.type fvarId) then
              lctx := lctx.erase fvarId
              let mvarId ← clear (← getMainGoal) fvarId
              replaceMainGoal [mvarId]
              loopMadeChange := true
        | none => continue
