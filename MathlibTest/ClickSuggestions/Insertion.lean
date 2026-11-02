module

public import Mathlib.Tactic.Common
public meta import Lean.Elab.Frontend

/-!
We test the logic that `#click_suggestions` uses to insert its suggestions into the source file.
To do this, we take command as a `String`, parse it and elaborate it,
and then run the insertion logic on the result at some given positions.
-/

meta section

open Lean Elab ProofWidgets Mathlib.Tactic.ClickSuggestions

def String.replaceRange (s newText : String) (range : Lean.Syntax.Range) : String :=
  Pos.Raw.extract s ⟨0⟩ range.start ++ newText ++ Pos.Raw.extract s range.stop ⟨s.utf8ByteSize⟩

def String.insertCursor (file : String) (cursorPos : String.Pos.Raw) : String :=
  file.replaceRange "∣" ⟨cursorPos, cursorPos⟩

def testInsertionLogic (tactic : CoreM (TSyntax `tactic))
    (cursorPosList : List Lsp.Position) (input : String) (onGoal : Nat := 0) :
    MetaM Unit := do
  let context := Parser.mkInputContext input (fileName := "<input>")
  let s ← IO.processCommands context {} (Command.mkState (← getEnv))
  let trees : List InfoTree := s.commandState.infoState.trees.toList
  let fileMap := context.fileMap
  let mut msgs := m!""
  for cursorPos in cursorPosList do
    let rawCursorPos := fileMap.lspPosToUtf8Pos cursorPos
    let some goalsAt := trees.findSome? (·.goalsAt? fileMap rawCursorPos |>.head?) |
      throwError m!"No goals at cursor position {cursorPos}"
    let goals :=
      if goalsAt.useAfter then goalsAt.tacticInfo.goalsAfter else goalsAt.tacticInfo.goalsBefore
    let (_, statusToken) ← mkRefreshComponent
    let (_, solvedToken) ← mkRefreshComponent
    let (_, masterToken) ← mkRefreshComponent
    let ctx := {
      fileMap, cursorPos, onGoal, goalsAt, masterToken, statusToken, solvedToken
      numGoals := goals.length
      fileVersion := { uri := default }
      goal := default, hyp? := default, pos := default
    }
    let go : ClickSuggestionsM String := do
      let (range, newText) ← mkInsertion (← tactic)
      let newPos := newCursorPos cursorPos range newText
      let output := input.replaceRange newText (fileMap.lspRangeToUtf8Range range)
      return output.insertCursor ((FileMap.ofString output).lspPosToUtf8Pos newPos)
    let output ← go.run ctx (← IO.mkRef {})
    msgs := msgs ++ m!"{input.insertCursor rawCursorPos}\n==>\n{output}\n---\n"
  logInfo msgs

local macro "#test" tac:term:max pos:term:max s:str : command =>
  `(command| run_meta testInsertionLogic $tac $pos $s)

-- The inserted tactic respects the 100 character line lenght limit:
/--
info: example : 1 + 1 = 2 ∧ True := by
  ∣
==>
example : 1 + 1 = 2 ∧ True := by
  rw [Nat.add_comm, Nat.add_comm, Nat.add_comm, Nat.add_comm, Nat.add_comm, Nat.add_comm,
    Nat.add_comm]∣
---
-/
#guard_msgs in
#test `(tactic|
  rw [$(mkIdent ``Nat.add_comm):ident, $(mkIdent ``Nat.add_comm):ident,
  $(mkIdent ``Nat.add_comm):ident, $(mkIdent ``Nat.add_comm):ident, $(mkIdent ``Nat.add_comm):ident,
  $(mkIdent ``Nat.add_comm):ident, $(mkIdent ``Nat.add_comm):ident]) [⟨1, 2⟩] "\
example : 1 + 1 = 2 ∧ True := by
  "


-- A focus dot is added if there are multiple goals or if the previous tactic was a `·`:
/--
info: example : 1 = 1 ∧ 1 = 1 := by
  constructor∣
==>
example : 1 = 1 ∧ 1 = 1 := by
  constructor
  · rfl∣
---
-/
#guard_msgs in
#test `(tactic| rfl) [⟨1, 13⟩] "\
example : 1 = 1 ∧ 1 = 1 := by
  constructor"

/--
info: example : 1 = 1 ∧ 1 = 1 := by
  constructor
  · rfl
  ∣
==>
example : 1 = 1 ∧ 1 = 1 := by
  constructor
  · rfl
  · simp
  ∣
---
-/
#guard_msgs in
#test `(tactic| simp) [⟨3, 2⟩] "\
example : 1 = 1 ∧ 1 = 1 := by
  constructor
  · rfl
  "


-- Subsequent rewriting tactics are merged, on the left and on the right.
/--
info: example : 1 + 1 = 2 ∧ True := by
  ∣rw [Nat.add_comm]

==>
example : 1 + 1 = 2 ∧ True := by
  rw [rfl, Nat.add_comm]∣

---
example : 1 + 1 = 2 ∧ True := by
  rw [Nat.add_comm]
∣
==>
example : 1 + 1 = 2 ∧ True := by
  rw [Nat.add_comm, rfl]
∣
---
-/
#guard_msgs in
#test `(tactic|
  rw [$(mkIdent ``rfl):ident]) [⟨1, 2⟩, ⟨2, 0⟩] "\
example : 1 + 1 = 2 ∧ True := by
  rw [Nat.add_comm]
"

/--
info: example : 1 + 1 = 2 ∧ True := by
  ∣simp_rw [Nat.add_comm]

==>
example : 1 + 1 = 2 ∧ True := by
  simp_rw [rfl, Nat.add_comm]∣

---
example : 1 + 1 = 2 ∧ True := by
  simp_rw [Nat.add_comm]
∣
==>
example : 1 + 1 = 2 ∧ True := by
  simp_rw [Nat.add_comm, rfl]
∣
---
-/
#guard_msgs in
#test `(tactic|
  simp_rw [$(mkIdent ``rfl):ident]) [⟨1, 2⟩, ⟨2, 0⟩] "\
example : 1 + 1 = 2 ∧ True := by
  simp_rw [Nat.add_comm]
"


/--
info: example : 1 + 1 = 2 ∧ True := by
  ∣grw [Nat.add_comm]

==>
example : 1 + 1 = 2 ∧ True := by
  grw [rfl, Nat.add_comm]∣

---
example : 1 + 1 = 2 ∧ True := by
  grw [Nat.add_comm]
∣
==>
example : 1 + 1 = 2 ∧ True := by
  grw [Nat.add_comm, rfl]
∣
---
-/
#guard_msgs in
#test `(tactic|
  grw [$(mkIdent ``rfl):ident]) [⟨1, 2⟩, ⟨2, 0⟩] "\
example : 1 + 1 = 2 ∧ True := by
  grw [Nat.add_comm]
"


-- Test the heuristic for where to insert and where to put the cursor afterwards.
/--
info: example : 1 + 1 = 2 := by∣
  skip
  skip
    ⏎
==>
example : 1 + 1 = 2 := by rfl∣
  skip
  skip
    ⏎
---
example : 1 + 1 = 2 := by
∣  skip
  skip
    ⏎
==>
example : 1 + 1 = 2 := by
rfl∣  skip
  skip
    ⏎
---
example : 1 + 1 = 2 := by
  ∣skip
  skip
    ⏎
==>
example : 1 + 1 = 2 := by
  rfl
  ∣skip
  skip
    ⏎
---
example : 1 + 1 = 2 := by
  skip
∣  skip
    ⏎
==>
example : 1 + 1 = 2 := by
  skip
  rfl
∣  skip
    ⏎
---
example : 1 + 1 = 2 := by
  skip
  ∣skip
    ⏎
==>
example : 1 + 1 = 2 := by
  skip
  rfl
  ∣skip
    ⏎
---
example : 1 + 1 = 2 := by
  skip
  sk∣ip
    ⏎
==>
example : 1 + 1 = 2 := by
  skip
  skip
  rfl∣
    ⏎
---
example : 1 + 1 = 2 := by
  skip
  skip∣
    ⏎
==>
example : 1 + 1 = 2 := by
  skip
  skip
  rfl∣
    ⏎
---
example : 1 + 1 = 2 := by
  skip
  skip
∣    ⏎
==>
example : 1 + 1 = 2 := by
  skip
  skip
  rfl
∣    ⏎
---
example : 1 + 1 = 2 := by
  skip
  skip
  ∣  ⏎
==>
example : 1 + 1 = 2 := by
  skip
  skip
  rfl
  ∣  ⏎
---
example : 1 + 1 = 2 := by
  skip
  skip
    ∣
==>
example : 1 + 1 = 2 := by
  skip
  skip
  rfl
    ∣
---
-/
#guard_msgs in
#test `(tactic| rfl) [⟨0, 25⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 4⟩, ⟨2, 6⟩, ⟨3, 0⟩, ⟨3, 2⟩, ⟨3, 4⟩] "\
example : 1 + 1 = 2 := by
  skip
  skip
    "
