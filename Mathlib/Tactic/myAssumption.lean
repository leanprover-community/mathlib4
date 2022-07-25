import Lean
import Mathlib.Tactic.Basic

def fib : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => fib (n + 1) + fib n

macro "custom_sorry" : tactic => `(tactic| sorry)

example : 1 = 42 := by
  sorry

syntax "custom_tactic" : tactic
macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)
macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

example : 42 = 42 := by
  rfl

example : 42 = 42 ∧ 43 = 43 := by
  custom_tactic

syntax tactic " and_then " tactic : tactic
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; all_goals $b:tactic)

example : 42 = 42 ∧ 43 = 43 := by
  apply And.intro and_then rfl

elab "custom_sorry_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← Lean.Meta.getMVarDecl goal
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"
    Lean.Elab.admitGoal goal

elab "list_local_decls" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM fun decl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      trace[Elab.debug] "{declExpr} : {declType}"

open Lean Elab.Tactic MonadLCtx Meta in
elab "myAssump" : tactic => do
  let target ← getMainTarget
  for ldecl in (← getLCtx) do
    if (← pure !ldecl.isAuxDecl <&&> isDefEq ldecl.type target) then
      closeMainGoal ldecl.toExpr
      return
  throwTacticEx `my_assumption (← getMainGoal)
    m!"unable to find matching hypothesis of type{indentExpr target}"

set_option trace.Elab.debug true in
def foo : 1 = 1 → 3 = 3 := by
  list_local_decls
  myAssump

/-! # MetaM examples -/

def f {α} [Add α] (x : α) : List α :=
  [x, x, x + x]

open Lean Lean.Meta in
def test : MetaM Unit := do
  let t ← mkAppM `f #[mkNatLit 3]
  trace[Meta.debug] "t: {t}"
  let t ← whnf t
  trace[Meta.debug] "after whnf: {t}"
  return

example (n : ℕ) : n = n := by
  rfl

open Lean Lean.Meta in
elab "myIntro" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainTarget
    let goalDecl ← Lean.Meta.getMVarDecl goal
    let goalType := goalDecl.type
    let lctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    match goalType with
    | .forallE name type body data =>
      let fvarId ← mkFreshFVarId
      let lctx   := lctx.mkLocalDecl fvarId `h type data.binderInfo
      Lean.Meta.throwTacticEx `myIntro goal
        (m!"boop")
    | _ => Lean.Meta.throwTacticEx `myIntro goal
            (m!"goal is not a Forall/Pi type")


-- #eval (`(20 < 5) : Lean.Expr)

example : ∀ n : ℕ, n = n := by
  myIntro
