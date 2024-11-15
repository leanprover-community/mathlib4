import Mathlib.Data.Seq.Seq
import Lean
import Lean.Elab.Tactic
import Mathlib.Tactic.Tendsto.Main

open Lean Lean.Expr Lean.Meta

open Stream' Seq

attribute [local irreducible] Seq.cons
attribute [local irreducible] Seq.nil
attribute [local irreducible] Seq.corec

open Lean open Meta

def someNumber : Nat := (· + 2) $ 3

#check Expr.const ``someNumber []
#eval Expr.const ``someNumber []
-- Lean.Expr.const `someNumber []

#eval reduce (Expr.const ``someNumber [])
-- Lean.Expr.lit (Lean.Literal.natVal 5)

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"{goalType}"
    -- dbg_trace ((← withTransparency .all $ reduce goalType))

    -- withTransparency .all do
    --   let reduced ← Lean.Meta.reduce goalType
    --   -- dbg_trace f!"goal type: {goalType}"
    --   let kek ← Lean.Meta.ppExpr reduced
    --   dbg_trace kek


def HasZero (s : Seq ℕ) : Prop := 0 ∈ s


theorem HasZero_nil : ¬ HasZero nil := by simp [HasZero]

theorem HasZero_cons {hd : ℕ} {tl : Seq ℕ} : HasZero (cons hd tl) ↔ (0 = hd) ∨ HasZero tl := by
  simp [HasZero]

theorem HasZero_of_destruct {s : Seq ℕ} : HasZero s ↔ (destruct s).elim False fun (hd, tl) =>
    0 = hd ∨ HasZero tl := by
  cases' s with hd tl
  · simp
    exact HasZero_nil
  · simp
    exact HasZero_cons

def s1 : Seq ℕ := cons 0 nil

example : HasZero s1 := by
  unfold s1 HasZero
  simp only [Seq.mem_cons]

def s2 : Seq ℕ := cons 1 (cons 0 nil)

example : HasZero s2 := by
  unfold s2 HasZero
  simp

def s3 : Seq ℕ := cons 2 <| cons 1 (cons 0 nil)

example : HasZero s3 := by
  simp [s3]
  rw [HasZero_of_destruct]
  conv in destruct _ => simp

abbrev my_nats : Seq ℕ := Seq.corec (fun (n : ℕ) => .some (n, n + 1)) 0

example : HasZero my_nats := by
  -- simp [my_nats]
  rw [HasZero_of_destruct]
  custom_sorry_1
  conv in destruct _ => simp
  simp only [Option.elim]
  simp
