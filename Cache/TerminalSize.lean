/-
Copyright (c) 2026 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/

/-! # Helper method for querying the size of the current terminal window

This module provides a helper method to query the size of the current terminal (if any).
The current implementation calls out to `stty`, in particular will only work on UNIX systems.

TODO: implement this robustly in a cross-platform way in Lean core, by using `uv_tty_get_winsize`.
This is tracked in RFC TODOLINK!

-/

/--
Terminal size as `(width, height)` in character cells by running `stty size`,
or `none` if there's no controlling terminal or `stty` is unavailable.

`stty` must inherit our real stdin to read the terminal, so this only works when
the current process's stdin is itself a tty.
-/
def getWindowSize : IO (Option (Nat × Nat)) := do
  let child ←
    try
      IO.Process.spawn {
        cmd    := "stty"
        args   := #["size"]
        stdin  := .inherit   -- stty queries the terminal via stdin
        stdout := .piped     -- capture "rows cols"
        stderr := .null      -- silence "stdin isn't a terminal"
      }
    catch _ =>
      return none            -- stty not found
  let out ← child.stdout.readToEnd
  if (← child.wait) != 0 then return none
  match out.trimAscii.toString.splitOn " " with
  | [rows, cols] =>
    match rows.toNat?, cols.toNat? with
    | some h, some w => return some (w, h)   -- stty prints rows first; return width first
    | _, _           => return none
  | _ => return none

-- def main : IO Unit := do
--   match ← getWindowSize with
--   | some (w, h) => IO.println s!"terminal is {w} columns wide, {h} rows tall"
--   | none        => IO.println "no terminal detected (stdin isn't a tty, or stty is missing)"
