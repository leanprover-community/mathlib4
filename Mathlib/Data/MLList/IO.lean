/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.MLList.Basic
import Mathlib.Lean.System.IO

/-!
# Reading from handles, files, and processes as lazy lists.
-/

set_option autoImplicit true

open System IO.FS

namespace MLList

variable [Monad m]

/-- Read lines of text from a handle, as a lazy list in `IO`. -/
def linesFromHandle (h : Handle) : MLList IO String :=
  MLList.iterate (do
    let line ← h.getLine
    -- This copies the logic from `IO.FS.lines`.
    if line.length == 0 then
      return none
    else if line.back == '\n' then
      let line := line.dropRight 1
      let line :=
        if System.Platform.isWindows && line.back == '\x0d' then line.dropRight 1 else line
      return some line
    else
      return some line)
  |>.takeWhile (·.isSome) |>.map (fun o => o.getD "")

/-- Read lines of text from a file, as a lazy list in `IO`. -/
def lines (f : FilePath) : MLList IO String := .squash fun _ => do
  return linesFromHandle (← Handle.mk f Mode.read)

open IO.Process in
/--
Run a command with given input on `stdio`,
returning `stdout` as a lazy list in `IO`.
-/
def runCmd (cmd : String) (args : Array String) (input : String := "") : MLList IO String := do
  let child ← spawn
    { cmd := cmd, args := args, stdin := .piped, stdout := .piped, stderr := .piped }
  linesFromHandle (← put child input).stdout
where put
    (child : Child { stdin := .piped, stdout := .piped, stderr := .piped }) (input : String) :
    IO (Child { stdin := .null, stdout := .piped, stderr := .piped }) := do
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  return child

/--
Variant of `MLList.fix?` that allows returning values of a different type.
-/
partial def fix?' [Monad m] (f : α → m (Option (α × β))) (init : α) : MLList m β :=
  squash fun _ => do
    match ← f init with
    | none => pure .nil
    | some (a, b) => pure (.cons b (fix?' f a))

/--
Give a list of tasks, return the monadic lazy list which
returns the values as they become available.
-/
def ofTaskList (tasks : List (Task α)) : MLList BaseIO α :=
  fix?' (init := tasks) fun t => do
    if h : 0 < t.length then
      let (a, t') ← IO.waitAny' t h
      pure (some (t', a))
    else
      pure none
