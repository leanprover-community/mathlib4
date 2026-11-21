/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Lean.Parser.Extension
public import Lean.PrettyPrinter.Formatter
public import Lean.PrettyPrinter.Parenthesizer
public import Mathlib.Tactic.Gavrilovich.Grid

/-!
# The block parser

The top-left corners `⌜ ┌ ╭` are the only tokens that diagrams add to Lean's token table. From
there a raw `ParserFn` runs `scanBlock` over the source text, jumps to the end of the block, and
pushes the whole block as one multi-line atom. Lean's tokenizer never sees anything inside the
block.
-/

public meta section

namespace Mathlib.Tactic.Gavrilovich
open Lean Parser PrettyPrinter

/-- Skip over the block starting at the current position, or fail at the first layout error. -/
def diagramScanFn : ParserFn := fun c s =>
  match scanBlock c.inputString s.pos.byteIdx with
  | .ok blk => s.setPos ⟨blk.stop⟩
  | .error e => s.mkUnexpectedErrorAt e.msg ⟨e.start⟩

/-- `diagramScanFn`, producing one atom for the whole block. -/
def diagramFn : ParserFn := rawFn diagramScanFn (trailingWs := true)

/-- A 2D diagram block, starting at `⌜` (or `┌`, `╭`). See `Mathlib.Tactic.Gavrilovich.Grid` for
its layout. -/
def diagram : Parser where
  fn := diagramFn
  info :=
    { collectTokens := (["⌜", "┌", "╭"] ++ ·), firstTokens := .tokens ["⌜", "┌", "╭"] }

/-- Format a diagram. A multi-row diagram starts on a new line, with all of its rows at the same
indentation, since the corners of a box must be aligned. -/
@[combinator_formatter diagram]
def diagram.formatter : Formatter := do
  let stx ← Syntax.MonadTraverser.getCur
  let .atom _ val := stx.ifNode (·.getArg 0) (fun _ => stx) |
    Formatter.visitAtom Name.anonymous
  unless val.contains '\n' do return ← Formatter.visitAtom Name.anonymous
  Formatter.indent (Formatter.pushToken .none ("\n" ++ val) false) (indent := some 2)
  Syntax.MonadTraverser.goLeft

@[combinator_parenthesizer diagram, inherit_doc diagram]
def diagram.parenthesizer : Parenthesizer := Parenthesizer.visitToken

end Mathlib.Tactic.Gavrilovich
