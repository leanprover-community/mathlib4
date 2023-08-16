import Mathlib.Util.Frontend
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Relation.Rfl
import Aesop
import Cli

open Lean Core Elab IO Meta Term Tactic -- All the monads!

inductive Result
| failure
| subgoals
| notDefEq
| success
deriving Repr, BEq

instance : ToString Result where
  toString := fun
  | .failure => "failure"
  | .subgoals => "subgoals"
  | .notDefEq => "notDefEq"
  | .success => "success"

/--
Compile the designated module, select declarations satisfying a predicate,
and run a tactic on the type of each declaration.
-/
def runTacticAtDecls (mod : Name) (decls : ConstantInfo → CoreM Bool) (tac : TacticM Unit) :
    IO (List (ConstantInfo × Result)) := do
  let steps ← compileModule mod
  if steps.any fun s => s.msgs.length > 0 then throw <| IO.userError s!"Unexpected messages in: {mod}"
  let env ← match steps.head? with
  | none => throw <| IO.userError s!"No commands in: {mod}"
  | some { before, .. } => pure before
  let decls' (i : ConstantInfo) : IO Bool := Prod.fst <$> (CoreM.toIO · { fileName := "", fileMap := default } {env}) do decls i
  -- Only look at the compilation steps in which we add a declaration satisfying `decls`.
  let targets := (← steps.mapM fun c =>
    c.diff.filterMapM fun i => do if ← decls' i then pure (some (c, i)) else pure none).join
  targets.mapM fun (cmd, ci) => do
    let ctx := { fileName := "", options := {}, fileMap := default }
    let state := { env := cmd.before }
    -- From `IO` to `CoreM`:
    Prod.fst <$> (CoreM.toIO · ctx state) do
      -- From `CoreM` to `MetaM`:
      MetaM.run' (ctx := {}) (s := {}) do
        let g ← mkFreshExprMVar ci.type
        -- From `MetaM` to `TermElabM`
        let gs ← try? <| TermElabM.run' do
          -- From `TermElabM` to `TacticM`!
          Tactic.run g.mvarId! tac
        match gs with
        | none => return (ci, .failure)
        | some (_ :: _) => return (ci, .subgoals)
        | some [] =>
          match ci.value? with
          | none => return (ci, .success)
          | some v =>
            if ← isDefEq g v then
              return (ci, .success)
            else
              return (ci, .notDefEq)

def introsAssumption : TacticM Unit := liftMetaTactic fun g => do
  let (_, g') ← g.intros
  g'.assumption
  pure []

def useAesop : TacticM Unit := do evalTactic (← `(tactic| aesop))
def useRfl : TacticM Unit := do evalTactic (← `(tactic| intros; rfl))
def useSimpAll : TacticM Unit := do evalTactic (← `(tactic| intros; simp_all))

-- #check Lean.EnvExtensionInterfaceUnsafe.getState

-- #eval show IO _ from do
--   let result ← runTacticAtDecls `Mathlib.Init.ZeroOne (fun n => true) a
--   return result.map fun (ci, r) => (ci.name, r)


-- #eval 1+1

open System
-- Next two declarations borrowed from `runLinter.lean`.
instance : ToExpr FilePath where
  toTypeExpr := mkConst ``FilePath
  toExpr path := mkApp (mkConst ``FilePath.mk) (toExpr path.1)

elab "compileTimeSearchPath%" : term =>
  return toExpr (← searchPathRef.get)

open Cli


/-- A custom command-line argument parser that allows either relative paths to Lean files,
(e.g. `Mathlib/Topology/Basic.lean`) or the module name (e.g. `Mathlib.Topology.Basic`). -/
instance : ParseableType Name where
  name     := "Name"
  parse? s :=
    if s.endsWith ".lean" then
      some <| (s : FilePath).withExtension "" |>.components.foldl Name.mkStr Name.anonymous
    else
      String.toName s


def runTacticMain (args : Cli.Parsed) : IO UInt32 := do
  let module := args.positionalArg! "module" |>.as! Name
  searchPathRef.set compileTimeSearchPath%
  let tac ←
    if args.hasFlag "aesop" then pure useAesop else
    if args.hasFlag "rfl" then pure useRfl else
    if args.hasFlag "simp_all" then pure useSimpAll else
    throw <| IO.userError "Specify a tactic, e.g. `--aesop`"
  let result ← runTacticAtDecls module (fun i => do pure ¬ (← i.name.isBlackListed)) tac
  IO.println s!"{module} {result.map (·.2) |>.count .success} {result.length}"
  return 0
  -- for (ci, r) in result do
  --   IO.println "---"
  --   IO.println ci.name
  --   IO.println ci.type
  --   IO.println r


/-- Setting up command line options and help text for `lake exe run_tactic`. -/
def run_tactic : Cmd := `[Cli|
  run_tactic VIA runTacticMain; ["0.0.1"]
  "Run a customisable tactic at all declarations in a file."

  FLAGS:
    "aesop";       "Use `aesop`."
    "rfl";         "Use `intros; rfl`."
    "simp_all";    "Use `intros; simp_all`."

  ARGS:
    module : Name; "Lean module to compile and export InfoTrees."
]

/-- `lake exe export_infotree` -/
def main (args : List String) : IO UInt32 :=
  run_tactic.validate args
