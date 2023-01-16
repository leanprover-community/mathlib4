import lean
open Lean Elab Std
set_option linter.unusedVariables false

theorem my_theorem : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)

partial def linearCore (expr0 : Expr) : MetaM Unit := do
  -- Create context0: no need to, because there are no loose bvars
  -- Log expr0: `fun p hP => hP` of type `∀ (p : Prop), p → p`
  let messageData := MessageData.ofExpr (expr0)
  Lean.logInfo m!"With context (none): {messageData}"

  match expr0 with
  | e@(Expr.lam varName varType body binderInfo) => do
    -- Create context1: context for free variable (p: Prop)
    Lean.Meta.withLocalDecl varName binderInfo varType fun x => do
      let expr1 := Expr.instantiate1 body x
      let context1 := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }

      -- Log expr1: `fun hP => hP` of type `p → p`
      let messageData := MessageData.withContext context1 (MessageData.ofExpr (expr1))
      Lean.logInfo m!"With context (p : Prop): {messageData}"

      match expr1 with
      | e@(Expr.lam varName varType body binderInfo) => do
        -- Create context2: Context for free variable (hP : p)
        Lean.Meta.withLocalDecl varName binderInfo varType fun x => do
          let expr2 := Expr.instantiate1 body x
          let context2 : MessageDataContext := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }

          -- Log expr2: `hP` of type `p`
          let messageData := MessageData.withContext context2 (MessageData.ofExpr (expr2))
          Lean.logInfo m!"With context (hP : p): {messageData}"
      | e => do
        dbg_trace "nothing"; return ()
  | e => do
    dbg_trace "nothing"; return ()


elab "#explode " theoremStx:ident : command => do
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  Elab.Command.liftCoreM do
    Lean.Meta.MetaM.run' do
      let results ← linearCore body

#explode my_theorem
