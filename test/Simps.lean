import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Simps
import Mathlib.Tactic.RunCmd

open Lean Meta Elab Term Command

run_cmd Command.runTermElabM fun _ => do
  let _ ← mkConditionalInstance (← elabTerm (← `(AddGroup Bool)) none)
    (← elabTerm (← `(Add Bool)) none)
  -- IO.println <| format e
  pure ()

structure Foo1 : Type where
  one : Nat
  two : Bool
  three : Nat → Bool
  four : 1 = 1
  five : 2 = 1

initialize_simps_projections Foo1 (one → toNat, two → toBool, three → coe as_prefix, -toBool)

run_cmd liftTermElabM <| do
  let  env ← getEnv
  let state := ((simpsStructure.getState env).find? `Foo1).get!
  -- IO.println <| format state
  guard <| state.1 == []
  guard <| state.2.map (·.1) == [`toNat, `toBool, `coe, `four, `five]
  liftMetaM <| guard (← isDefEq (state.2.head!.2) (← elabTerm (← `(Foo1.one)) none))
  liftMetaM <| guard (← isDefEq (state.2.tail.head!.2) (← elabTerm (← `(Foo1.two)) none))
  guard <| state.2.map (·.3) == (List.range 5).map ([·])
  guard <| state.2.map (·.4) == [true, false, true, false, false]
  guard <| state.2.map (·.5) == [false, false, true, false, false]
  pure ()

structure Foo2 (α : Type _) : Type _ where
  elim : α × α

def Foo2.simps.elim (α : Type _) : Foo2 α → α × α := fun x => (x.elim.1, x.elim.2)

initialize_simps_projections Foo2

-- run_cmd liftTermElabM <| do
--   let  env ← getEnv
--   let state := ((simpsStructure.getState env).find? `Foo2).get!
--   IO.println <| format state

structure Left (α : Type _) extends Foo2 α where
  moreData1 : Nat
  moreData2 : Nat

initialize_simps_projections Left

structure Right (α : Type u) (β : Type v) extends Foo2 α where
  otherData : β

initialize_simps_projections Right (toFoo2_elim → newProjection)

run_cmd liftTermElabM <| do
  let  env ← getEnv
  let state := ((simpsStructure.getState env).find? `Right).get!
  -- IO.println <| format state
  guard <| state.1 == [`u, `v]
  guard <| state.2.map (·.1) == [`toFoo2, `otherData, `newProjection]
  guard <| state.2.map (·.3) == [[0],[1],[0,0]]
  guard <| state.2.map (·.4) == [true, true, true]
  guard <| state.2.map (·.5) == [false, false, false]

structure Top (α β : Type _) extends Left α, Right α β

initialize_simps_projections Top

structure NewTop (α β : Type _) extends Right α β, Left α

def NewTop.simps.newElim {α β : Type _} (x : NewTop α β) : α × α := x.elim

-- initialize_simps_projections? NewTop (toRight_toFoo2_elim → newElim)
