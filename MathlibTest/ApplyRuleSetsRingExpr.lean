module

public import MathlibTest.ApplyRuleSetsRegister

open Mathlib.Tactic.ApplyRuleSets

inductive RingExpr where
  | var (n : Nat)
  | neg (a : RingExpr)
  | add (a b : RingExpr)
  | sub (a b : RingExpr)
  | mul (a b : RingExpr)

variable {α : Type*} [Inhabited α] [Neg α] [Add α] [Sub α] [Mul α]

def RingExpr.interpret (expr : RingExpr) (atoms : List α) : α :=
  match expr with
  | var i =>
    if h : i < atoms.length then
      atoms[i]
    else
      default
  | neg a => - a.interpret atoms
  | add a b => a.interpret atoms + b.interpret atoms
  | sub a b => a.interpret atoms - b.interpret atoms
  | mul a b => a.interpret atoms * b.interpret atoms

def HasRingExpr (atoms : List α) (e : α) (expr : RingExpr) : Prop :=
  expr.interpret atoms = e

namespace HasRingExpr
-- parse_expr

theorem expr_congr {atoms : List α} {x : α} {expr expr' : RingExpr}
    (h : HasRingExpr atoms x expr) (h' : expr = expr') : HasRingExpr atoms x expr' := by
  subst h'
  exact h

@[parse_expr]
theorem neg (atoms : List α) (x : α) (e : RingExpr) (h : HasRingExpr atoms x e) :
    HasRingExpr atoms (-x) (.neg e) := by
  simp [HasRingExpr, RingExpr.interpret] at h ⊢
  exact congrArg Neg.neg h

@[parse_expr]
theorem add (atoms : List α) (x y : α) (ex ey : RingExpr)
    (hx : HasRingExpr atoms x ex) (hy : HasRingExpr atoms y ey) :
    HasRingExpr atoms (x + y) (.add ex ey) := by
  simp [HasRingExpr, RingExpr.interpret] at hx hy ⊢
  rw [hx, hy]

@[parse_expr]
theorem sub (atoms : List α) (x y : α) (ex ey : RingExpr)
    (hx : HasRingExpr atoms x ex) (hy : HasRingExpr atoms y ey) :
    HasRingExpr atoms (x - y) (.sub ex ey) := by
  simp [HasRingExpr, RingExpr.interpret] at hx hy ⊢
  rw [hx, hy]

@[parse_expr]
theorem mul (atoms : List α) (x y : α) (ex ey : RingExpr)
    (hx : HasRingExpr atoms x ex) (hy : HasRingExpr atoms y ey) :
    HasRingExpr atoms (x * y) (.mul ex ey) := by
  simp [HasRingExpr, RingExpr.interpret] at hx hy ⊢
  rw [hx, hy]


open Lean Meta Mathlib.Tactic.ApplyRuleSets in
@[parse_expr high]
ruleproc collect_atoms (atoms : List α) (e : α) (expr : RingExpr) : HasRingExpr atoms e expr :=
  fun argOrigin goal => do
    let atoms ← instantiateMVars atoms
    let e ← instantiateMVars e
    let expr ← instantiateMVars expr

    -- figure out atoms
    if atoms.isMVar && ¬e.isMVar then
      let fvars := (← (e.collectFVars.run {})).2.fvarIds

      let mut xs ← mkAppOptM ``List.nil #[α]
      for id in fvars do
        let t ← id.getType
        if ← isDefEq t α then
          xs := ← mkAppM ``List.cons #[.fvar id, xs]

      atoms.mvarId!.assign xs
      return ← applyRuleSets argOrigin goal

    -- figure out atom index
    if ¬atoms.isMVar && e.isFVar && expr.isMVar then
      let rec getAtoms (atoms : Expr) (atomsFVars : Array FVarId) : Option (Array FVarId) := do
        match atoms with
        | mkApp3 (.const ``List.cons _) _ (.fvar id) atoms' =>
          getAtoms atoms' (atomsFVars.push id)
        | Expr.app (Expr.const ``List.nil _) _  => some atomsFVars
        | _ => none

      let some atomsFVars := getAtoms atoms #[] | return none
      let .fvar id := e | return none

      let some i := atomsFVars.idxOf? id | return none

      let exprVal ← mkAppM ``RingExpr.var #[mkNatLit i]
      expr.mvarId!.assign exprVal

      let prf ← mkFreshExprMVar goal
      try
        prf.mvarId!.refl
        return prf
      catch _ =>
        pure ()
    return none


variable (x y : Int)

example : HasRingExpr [x, y] x (.var 0) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl

example : HasRingExpr [x, y] y (.var 1) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl

example : HasRingExpr [x, y] (-x) (.neg (.var 0)) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl

example : HasRingExpr [x, y] (x + y) (.add (.var 0) (.var 1)) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl

example : HasRingExpr [x, y] (x - y) (.sub (.var 0) (.var 1)) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl

example : HasRingExpr [x, y] (x * y) (.mul (.var 0) (.var 1)) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl

example : HasRingExpr [x, y] ((x + y) * (-x - y))
    (.mul (.add (.var 0) (.var 1)) (.sub (.neg (.var 0)) (.var 1))) := by
  apply HasRingExpr.expr_congr
  apply_rulesets [parse_expr]
  rfl


variable (x y z : Int)

set_option pp.proofs false
#check (by apply_rulesets [parse_expr] : HasRingExpr _ (x + y * z) _)
