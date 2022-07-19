import Lean
import Lean.Util.FoldConsts

open Lean Meta Elab Tactic

#check Expr

/-- Returns true if any of the names in the given `name_set` are present in the given `expr`. -/
def Lean.Expr.hasLocalIn (e : Expr) (ns : NameSet) : Bool :=
Option.isSome <| e.find? fun j =>
  match j with
    | Expr.fvar id => ns.contains id.name
    | _ => false



example (a b c: Nat) : true := by
  testtac a = b, a
  trivial
/--
`type_has_local_in_name_set h ns` returns true iff the type of `h` contains a
local constant whose unique name appears in `ns`.
-/
def typeHasLocalInNameSet (h : Expr) (ns : NameSet) : MetaM Bool := do
  let hType ← inferType h
  return hType.hasLocalIn ns

partial def revertTargetDeps : TacticM Nat := do
  let tgt ← getMainTarget
  let mut l : List FVarId := []
  for e in (← getLCtx) do
    l := if (← exprDependsOn tgt e.fvarId) then l.concat e.fvarId else l
  let (fvarIds, g) ← Meta.revert (← getMainGoal) l.toArray
  replaceMainGoal [g]
  match l with
  | [] => return fvarIds.size
  | _  => return fvarIds.size + (← revertTargetDeps)

#check FVarId.name

-- meta def revert_target_deps : tactic ℕ :=
-- do tgt ← target,
--    ctx ← local_context,
--    l ← ctx.mfilter (kdepends_on tgt),
--    n ← revert_lst l,
--    if l = [] then return n
--      else do m ← revert_target_deps, return (m + n)

elab (name := testtac) "testtac" h:term " , " ids:(colGt ident)* : tactic => do
  let hElab ← elabTerm h none
  let ids ← getFVarIds ids
  -- let ns := ids.foldl (fun s i => s.insert i.name) NameSet.empty
  dbg_trace (← revertTargetDeps)
  -- guard <| hElab.hasLocalIn ns


example (a b c: Nat) : a = b := by
  testtac a = b, a b

#check exprDependsOn
