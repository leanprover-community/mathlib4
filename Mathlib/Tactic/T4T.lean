import Lean.Elab.Term
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
import Batteries.CodeAction -- to enable the hole code action
import Lean.Meta.Tactic.Grind.Main

open Lean Elab Term Command Linter

register_option linter.t4t : Bool := {
  defValue := true
  descr := "enable transformations for tactics"
}

namespace T4T

/-- Output for the tactic transformer. -/
abbrev Out := Std.HashMap String.Range Syntax

def filterTactics (_stx : Syntax) (acc : Out) (tree : InfoTree) : CommandElabM Out := do
  -- Turn the CommandElabM into a surrounding context for traversing the tree.
  let ctx ← read
  let state ← get
  let ctxInfo := { env := state.env, fileMap := ctx.fileMap, ngen := state.ngen }
  -- TODO: is an accumulator a good idea here? Or should we merge the maps?
  let f ← tree.visitM (ctx? := some ctxInfo)
    (fun _ _ _ => pure true) -- TODO: skip if it doesn't match the range of `stx`.
    (fun ctx i _c cs => do
      -- Accumulate intermediate results.
      let fAcc : Out → Out := cs.foldl (init := id) (fun acc f => f.getD id ∘ acc)
      -- Should we addd the current piece of syntax?
      if let .ofTacticInfo i := i then
        let stx := i.stx
        let kind := stx.getKind
        if let some r := stx.getRange? true then
          -- TODO: customizability for the line below.
          -- This only works for 1 tactic, not a sequence.
          let trigger := kind == `linarith
          if trigger then
            if let [goal] := i.goalsBefore then -- TODO: support more than 1 goal. Probably by requiring all tests to succeed in a row
              let mctx := i.mctxBefore
              let lctx := (mctx.decls.find! goal).2
              let (test, msgs) ← ctx.runMetaM lctx do
                let test ← TermElabM.run' do
                  -- Make a fresh metavariable because the original goal is already assigned.
                  let type ← goal.getType
                  let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
                  -- Call grind
                  let params ← Meta.Grind.mkParams {}
                  let result ← Meta.Grind.main goal.mvarId! params (pure ())
                  logInfoAt stx (← result.toMessageData)
                  pure !result.hasFailed
                let msgs ← Core.getMessageLog
                return (test, msgs)
              modify (fun state => { state with messages := state.messages ++ msgs })
              if test then
                return (fun acc => acc.insert r stx) ∘ fAcc
      return fAcc)
  return f.getD id acc

def filterTacticsList (stx : Syntax)
    (trees : PersistentArray InfoTree) (acc : Out) : CommandElabM Out :=
  trees.foldlM (filterTactics stx) acc

/-- T4T (Transformations for Tactics) is the working title for a tactic analysis framework.
It is aimed at allowing developers to specify refactoring patterns,
which will be tested against a whole project,
to report proposed changes.

The overall design will have three user-supplied components:

  * **trigger** on a piece of syntax (which could contain multiple tactic calls);
  * **test** if a suggested change is indeed an improvement;
  * **tell** the user where changes can be made.

It hooks into the linting system to move through the infotree,
collecting tactic syntax and state to pass to the three Ts.
-/
def t4t : Linter where run := withSetOptionIn fun stx => do
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  /-
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  -/
  let trees ← getInfoTrees
  let map ← filterTacticsList stx trees {}
  let unused := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.t4t stx m!"'{stx}' can be replaced with 'grind'"
    last := r

initialize addLinter t4t

end T4T
