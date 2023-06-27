/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Lean.Expr.Traverse
import Mathlib.Control.Basic

/-!
# The `check_instances` tactic

Resynthesizes all typeclasses in the goal,
and reports for each whether this succeeds,
and if so how closely it matches the original.
-/
open Lean Elab Meta Tactic
namespace Lean.Expr

/--
Visit every typeclass instance in the `Expr`, calling a function `f` at each.
-/
def visitInstances (f : α → Expr → MetaM α) (init : α) (e : Expr) : MetaM α := do
  e.traverse (init := init) fun a i => do
    let ty ← inferType i
    if ¬ ty.isForall && (← isClass? ty).isSome then
       f a i
    else
      pure a

/--
Result type for `checkInstance`.
Records whether an instance can be resynthesized,
and if so how closely it matches the original.
-/
inductive CheckInstance
| failed
| not_defeq (i : Expr)
| defeq (i : Expr)
| defeq_reducible (i : Expr)
| exact (i : Expr)

/--
Attempt to resynthesize a typeclass, reporting whether this is possible,
and if so how closely it matches the original.
-/
def checkInstance (e : Expr) : MetaM CheckInstance := do
  if let .some t ← try? (do synthInstance (← inferType e)) then
    if e == t then
      return .exact t
    if ← withReducibleAndInstances <| isDefEq e t then
      return .defeq_reducible t
    else if ← isDefEq e t then
      return .defeq t
    else
      return .not_defeq t
  else
    return .failed

/--
Find all typeclass instances in an expression, and try resynthesizing them,
reporting whether this is possible and if so how closely it matches the original.
-/
def checkInstances (e : Expr) : MetaM (Array (Expr × CheckInstance)) :=
  e.visitInstances (init := #[]) fun a i => return a.push ⟨i, ← checkInstance i⟩

end Lean.Expr

/--
A tactic for resynthesizing all typeclass instances in the goal,
reporting if they can be resynthesized, and if so how closely they match the original terms.
-/
elab "check_instances" : tactic => do
  let results ← (← getMainTarget).checkInstances
  for ⟨e, r⟩ in results do
    match r with
    | .failed =>
        logInfo m!"💥: failed to resynthesize {← inferType e}"
    | .not_defeq i =>
        logInfo m!"❌: resynthesized {← inferType e}, but found\n  {i} != {e}"
    | .defeq i =>
        logInfo m!"🟡: resynthesized {← inferType e}, up to defeq\n  {i} vs {e}"
    | .defeq_reducible i =>
        logInfo m!"✅: resynthesized {← inferType e}, up to reducible defeq:\n  {i} vs {e}"
    | .exact _ =>
        logInfo m!"✅: resynthesized {← inferType e}"
