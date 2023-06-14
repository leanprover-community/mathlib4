import Std.Data.List.Basic

namespace Lean.Elab.Tactic

open Meta

def revertVarsOnce : TacticM (Array FVarId × List LocalDecl × MVarId) := focus do
  let ctx := (← getLCtx).decls.toList.reduceOption
  let gMVar := ← getMainGoal
  let goal := ← getMainTarget
  let foundDecls := (ctx.map fun x =>
    if (goal.find? (. == x.toExpr)).isSome then some x else none).reduceOption
  let fvarIdFound := (foundDecls.map Lean.LocalDecl.fvarId).toArray
  let (fvs, newGoal) := ← gMVar.revert fvarIdFound
  setGoals [newGoal]
  pure (fvs, ctx, newGoal)

partial
def revertLoop : TacticM (List LocalDecl × MVarId) := focus do
  let (fvars, ctx, newGoal) := ← revertVarsOnce
  if fvars.size == 0 then pure (ctx, newGoal) else revertLoop

def revertNMLoop (n m : Nat) : TacticM (List LocalDecl × MVarId) := do
  match n with
  | 0     => revertLoop
  | 1     => do let goal := ← getMainGoal; pure ([], goal)
  | n + 1 => focus do
    let (fvars, ctx, newGoal) := ← revertVarsOnce
--    logInfo m!"fvs: {fvars.size}"
--    let decl := ← fvars.mapM (Lean.FVarId.getDecl ·)
--    dbg_trace Format.pretty f!"{decl.map LocalDecl.userName}"
    if fvars.size == 0 then
      logInfo m!"{m} iterations would have sufficed.\nTry this: prunne {m}"
      pure (ctx, newGoal) else revertNMLoop n (m + 1)

/-
def revertNLoop (n : Nat) : TacticM (List LocalDecl × MVarId) := do
  let mut m := 0; match n with
  | 0     => revertLoop
  | 1     => do let goal := ← getMainGoal; pure ([], goal)
  | n + 1 => dbg_trace m; focus do
    let m := n;
    let (fvars, ctx, newGoal) := ← revertVarsOnce
    if fvars.size == 0 then
      logInfo m!"{m} iterations would have sufficed -- "
      pure (ctx, newGoal) else revertNLoop n
-/
/-
  if n == 0 then revertLoop else
  if n == 1 then do let goal := ← getMainGoal; pure ([], goal) else

  focus do
    let m := n;
    let (fvars, ctx, newGoal) := ← revertVarsOnce
    if fvars.size == 0 then
      logInfo m!"{m} iterations would have sufficed -- "
      pure (ctx, newGoal) else revertNLoop n
--  for i in [:n] do

#exit
-/


def pruneTac : TacticM Unit := focus do
  let dcls := (← getLCtx).decls.toList.reduceOption
  let goal := ← getMainGoal
  let newGoal ← goal.tryClearMany (dcls.map LocalDecl.fvarId).toArray
  setGoals [newGoal]
  let nms := (← getMainTarget).getForallBinderNames
  let (_newfvs, rGoal) := ← introNCore newGoal nms.length [] True True
  setGoals [rGoal]

elab "prune" : tactic => do
  let _ := ← revertLoop
  pruneTac

elab "prunne" n:num : tactic => do
  let _ := ← revertNMLoop n.getNat 0
  pruneTac

end Lean.Elab.Tactic

universe u
variable {α : Type u} [Add α] [Add α] {e f : α} {a b _d : Nat} {_h : e ≠ f} (h₁ : a = b)
  (h₂ : ff = b) {c : Int}

example : a + 5 = c ∨ True := by
  prunne 5
  /- goal state:
  b a: Nat
  h₁: a = b
  c: Int
  ⊢ Int.ofNat a + 5 = c ∨ True
  -/
  exact Or.inr trivial

/-- Lots of duplication of variables, since they are included *again*! -/
example {α : Type u} [Add α] [OfNat α 0] {e f : α} {a b _d : Nat} {_h : e ≠ f} (_h₁ : a = b)
  {_c : Int} : e + f = e ∨ True := by
  /- goal state:
  α✝: Type u
  inst✝³ inst✝²: Add α✝
  e✝ f✝: α✝
  a✝ b✝ _d✝: Nat
  _h✝: e✝ ≠ f✝
  h₁: a✝ = b✝
  c: Int
  α: Type u
  inst✝¹: Add α
  inst✝: OfNat α 0
  e f: α
  a b _d: Nat
  _h: e ≠ f
  _h₁: a = b
  _c: Int
  ⊢ e + f = e ∨ True
  -/
  prune
  /- goal state:
  α: Type u
  inst✝¹: Add α
  inst✝: OfNat α 0
  e f: α
  _h: e ≠ f
  ⊢ e + f = e ∨ True
  -/
  exact Or.inr trivial

example (a : Nat) : ∃ n, n = 0 := by
  constructor
  /-
  2 goals
  case h
  a: ℕ
  ⊢ ?w = 0
  case w
  a: ℕ
  ⊢ ℕ
  -/
  prune

  sorry
  prune
  /-
  1 goal
  case h
  a: ℕ
  ⊢ ?w = 0
  -/
