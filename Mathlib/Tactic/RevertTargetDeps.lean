import Lean
import Lean.Util.FoldConsts

open Lean Meta Elab Tactic

partial def revertTargetDepsImpl : TacticM Nat := do
  let tgt ← getMainTarget
  let l : List FVarId ← (← getLCtx).foldrM (init := []) fun dcl l => do
    if (← exprDependsOn tgt dcl.fvarId) then pure (dcl.fvarId::l) else pure l
  let (fvarIds, g) ← Meta.revert (← getMainGoal) l.toArray
  replaceMainGoal [g]
  match l with
  | [] => return fvarIds.size
  | _  => return fvarIds.size + (← revertTargetDepsImpl)

elab (name := revertTargetDeps) "revert_target_deps" : tactic => do
  let _ ← revertTargetDepsImpl; pure ()



-- these instances are needed for the example below

instance (p : Bool → Prop) [hd : DecidablePred p] : Decidable (∀ b, p b) :=
match hd true, hd false with
| Decidable.isFalse ht, _ => Decidable.isFalse fun ha => ht (ha _)
| _, Decidable.isFalse hf => Decidable.isFalse fun ha => hf (ha _)
| Decidable.isTrue ht, Decidable.isTrue hf => Decidable.isTrue <| Bool.rec hf ht

instance (p : Bool → Prop) [hd : DecidablePred p] : Decidable (∃ b, p b) :=
match hd true, hd false with
| Decidable.isFalse ht, Decidable.isFalse hf => Decidable.isFalse fun ⟨b, hb⟩ =>
  by cases b <;> contradiction
| Decidable.isTrue ht, _ => Decidable.isTrue ⟨_, ht⟩
| _, Decidable.isTrue hf => Decidable.isTrue ⟨_, hf⟩

-- this example is taken from the test file for revert_target_deps in mathlib
example (b : Bool) (h : b = true) : true := by
  let b₁ : Bool := b
  /-
  This test shows that `tactic.revert_target_deps`
  will revert `b₁` because it occurse in the `have` statement below,
  but recursively also reverts `b` (and hence `h`),
  because `b` occurs in the body of the `let` statement that introduces `b₁`,
  even though `b` doesn't occur directly in the `have` statement below.
  -/
  have : ∀ b₂ : Bool, b₂ ≠ b₁ → b₂ = false := by
    revert_target_deps
  -- ∀ (b : Bool),
  -- b = true →
  --   let b₁ := b;
  --   ∀ (b₂ : Bool), b₂ ≠ b₁ → b₂ = false
    decide
  trivial
