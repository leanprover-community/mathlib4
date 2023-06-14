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

def revertNLoop (n m : Nat) : TacticM (List LocalDecl × MVarId) := do
  match n with
  | 0     => revertLoop
  | 1     => do let goal := ← getMainGoal; pure ([], goal)
  | n + 1 => focus do
    let (fvars, ctx, newGoal) := ← revertVarsOnce
    if fvars.size == 0 then
      logInfo m!"{m} iterations suffice.\nTry this: prunne {m}"
      pure (ctx, newGoal) else revertNLoop n (m + 1)

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
  let _ := ← revertNLoop n.getNat 0
  pruneTac

syntax "prunne" (num)? : tactic

elab_rules : tactic
  | `(tactic| prunne $[$n]?) => do
    let _ := ← revertNLoop (n.getD default).getNat 0
    pruneTac

--elab "prunne" (n:num)? : tactic => do
--  let _ := ← revertNLoop n.getNat 0
--  pruneTac

end Lean.Elab.Tactic

universe u
variable {α : Type u} [Add α] [Add α] {e f : α} {a b _d : Nat} {_h : e ≠ f} (h₁ : a = b)
  (h₂ : ff = b) {c : Int}
set_option pp.rawOnError true
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
  prunne
  /- goal state:
  α: Type u
  inst✝¹: Add α
  inst✝: OfNat α 0
  e f: α
  _h: e ≠ f
  ⊢ e + f = e ∨ True
  -/
  exact Or.inr trivial

example (a : Nat) : ∃ n, n + 1 = 0 := by
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
  prunne

  sorry
  prunne 0

  /-
  1 goal
  case h
  a: ℕ
  ⊢ ?w = 0
  -/
