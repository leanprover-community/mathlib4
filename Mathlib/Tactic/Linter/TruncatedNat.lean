import Lean
import Batteries
import Qq

section

open Lean Meta Elab.Tactic Qq

def containsNaturalSubtraction : Expr → Bool
  | .app (.app (.const ``HSub.hSub _) (.const ``Nat _)) _ => true
  | .app f a => containsNaturalSubtraction f || containsNaturalSubtraction a
  | .lam _ _ b _ => containsNaturalSubtraction b
  | .forallE _ _ b _ => containsNaturalSubtraction b
  | .letE _ _ v b _ => containsNaturalSubtraction v || containsNaturalSubtraction b
  | _ => false

def checkIfNaturalSubtraction : TacticM Bool := do
  withMainContext do
    logInfo "Checking if the goal or local context contains natural subtraction"
    let goal ← getMainGoal
    logInfo m!"Checking goal: {goal}"
    let type ← goal.getType
    if containsNaturalSubtraction type then
      logInfo m!"ALERT: Goal contains natural subtraction: {type}"
      return true
    let ctx ← getLCtx
    for (decl : LocalDecl) in ctx do
      if containsNaturalSubtraction decl.type then
        logInfo m!"ALERT: Local declaration of type {decl.type} contains natural subtraction."
        return true
    logInfo "No natural subtraction found in goal or local context"
    return false

def containsNaturalDivision : Expr → Bool
  | .app (.app (.const ``HDiv.hDiv _) (.const ``Nat _)) _ => true
  | .app f a => containsNaturalDivision f || containsNaturalDivision a
  | .lam _ _ b _ => containsNaturalDivision b
  | .forallE _ _ b _ => containsNaturalDivision b
  | .letE _ _ v b _ => containsNaturalDivision v || containsNaturalDivision b
  | _ => false

def checkIfNaturalDivision : TacticM Bool := do
  withMainContext do
    logInfo "Checking if the goal or local context contains natural division"
    let goal ← getMainGoal
    logInfo m!"Checking goal: {goal}"
    let type ← goal.getType
    if containsNaturalDivision type then
      logInfo m!"ALERT: Goal contains natural division: {type}"
      return true
    let ctx ← getLCtx
    for (decl : LocalDecl) in ctx do
      if containsNaturalDivision decl.type then
        logInfo m!"ALERT: Local declaration of type {decl.type} contains natural division."
        return true
    logInfo "No natural division found in goal or local context"
    return false

end

-- example (a b : Nat) (h : a / b = 0) : 2 = 3 := by
--   run_tac
--     checkIfNaturalSubtraction
--   run_tac
--     checkIfNaturalDivision
--   sorry
