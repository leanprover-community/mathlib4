import Mathlib.Order.Defs.LinearOrder
import Mathlib.Lean.Exception
import Mathlib.Tactic.ReduceModChar.Ext
import Qq.MetaM
open Qq Lean Meta Elab Command ToAdditive

set_option autoImplicit true
-- work in a namespace so that it doesn't matter if names clash
namespace Test

-- [note] use the below options for diagnostics:
-- set_option trace.to_additive true
-- set_option trace.to_additive_detail true
-- set_option pp.universes true
-- set_option pp.explicit true
-- set_option pp.notation false

-- run_cmd do
--   unless ToAdditive.findTranslation? (← Lean.getEnv) ToAdditive.orderDualTranslations `Test.MulInd.one == some `Test.AddInd.zero do throwError "1"

section

open Qq Lean Meta Elab Command ToAdditive
universe u_1
-- set_option pp.privateNames true
run_cmd do
  logInfo m!"{orderDualBundle.reorderAttr.find? (← getEnv) `LE.le}"
  logInfo m!"{orderDualBundle.reorderAttr.find? (← getEnv) `LE.le}"
  logInfo m!"{orderDualBundle.reorderAttr.find? (← getEnv) `LE.le}"
  logInfo m!"{orderDualBundle.reorderAttr.find? (← getEnv) `LE.le}"

@[to_dual?]
def maxDefault' [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then b else a

@[to_dual? blah]
def blub {p : Type} [LE p] [DecidableRel ((· ≤ ·) : p → p → Prop)] (a b : p) (h : a ≤ b) :=
  a ≤ b

run_cmd do
  let e : Expr := q({α : Type} → [self : LE α] → (x1 x2 : α) → @LE.le α self x1 x2)
  let _ ← liftCoreM <| MetaM.run' <| applyReplacementFun orderDualBundle e

run_cmd do
  let e : Expr := q({α : Type} → [self : LinearOrder α] → (x1 x2 : α) → x1 ≤ x2)
  let _ ← liftCoreM <| MetaM.run' <| applyReplacementFun orderDualBundle e

run_cmd do
  let e : Expr := q({α : Type} → [self : LinearOrder α] → DecidableRel fun (x1 x2 : α) ↦ x1 ≤ x2)
  let _ ← liftCoreM <| MetaM.run' <| applyReplacementFun orderDualBundle e

end
