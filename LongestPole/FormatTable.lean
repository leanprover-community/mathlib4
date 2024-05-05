/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.String.Defs


/-!
# Format Table

This file provides a simple function for formatting a 2d array of strings into a markdown-compliant table.
-/

inductive Alignment where
  | left
  | right
  | center
deriving Inhabited, BEq

/--
Takes a 2d array of string data and renders it into a table.
 -/
def formatTable (headers : Array String) (table : Array (Array String))
    (alignments : Option (Array Alignment) := none) :
    String := Id.run do
  -- If no alignments are provided, default to left alignment for all columns
  let alignments := alignments.getD (Array.mkArray headers.size Alignment.left)
  -- Get the maximum widths of each column
  let mut widths := headers.map (·.length)
  for row in table do
    for i in [0:widths.size] do
      widths := widths.set! i (max widths[i]! ((row[i]?.map (·.length)).getD 0))
  -- Pad each cell with spaces to match the column width
  let paddedHeaders := headers.mapIdx fun i h => h.rightpad widths[i]!
  let paddedTable := table.map fun row => row.mapIdx fun i cell =>
    if alignments[i]! == Alignment.left then cell.rightpad widths[i]!
    else if alignments[i]! == Alignment.right then cell.leftpad widths[i]!
    else
      String.replicate ((widths[i]! - cell.length) / 2) ' '
      ++ cell
      ++ String.replicate ((widths[i]! - cell.length + 1) / 2) ' '
  -- Construct the lines of the table
  let headerLine := "| " ++ String.intercalate " | " (paddedHeaders.toList) ++ " |"
  -- Construct the separator line, with colons to indicate alignment
  let separatorLine :=
    "| "
    ++ String.intercalate " | "
        (((widths.zip alignments).map fun ⟨w, a⟩ =>
              if a == Alignment.left then ":" ++ String.replicate (w-1) '-'
              else if a == Alignment.right then String.replicate (w-1) '-' ++ ":"
              else ":" ++ String.replicate (w-2) '-' ++ ":"
              ).toList)
    ++ " |"
  let rowLines := paddedTable.map (fun row => "| " ++ String.intercalate " | " (row.toList) ++ " |")
  -- Return the table
  return String.intercalate "\n" (headerLine :: separatorLine :: rowLines.toList)
