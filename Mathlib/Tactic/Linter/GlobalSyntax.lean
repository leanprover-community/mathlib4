/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Import
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
#  The "globalSyntax" linter

The "globalSyntax" linter emits a warning on pairs of consecuting commands with no overall effect.

For instance, the linter would flag
```lean4
namespace X
end X
```
and similarly for consecutive pairs of `open` or `section` and `end`.
-/

public meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The `globalSyntax` linter emits a warning on pairs of consecutive commands with no overall effect.
For instance, the linter would flag
```lean4
namespace X
end X
```
and similarly for consecutive pairs of `open` or `section` and `end`.
-/
public register_option linter.globalSyntax : Bool := {
  defValue := true
  descr := "enable the globalSyntax linter"
}
/--
`RangesToKinds` stores bookkeeping information needed by the linter.

* `toKinds` maps the source `Syntax.Range` of a top-level command to its `SyntaxNodeKind`
  preserving enough information to detect cancelling pairs.
* `mod2` tracks the parity of coverage over the file by toggling both the start and stop
  positions of every encountered command range; once all top-level commands have been seen,
  this set should contain exactly the file’s import-end position and the final end-of-input.
* `importEnd` is the position immediately after the import block (computed using `parseImports`),
  used as one of the two distinguished positions in `mod2`.
-/
structure RangesToKinds where
  toKinds : Std.HashMap Syntax.Range Name
  mod2 : Std.HashSet String.Pos.Raw
  importEnd : Option String.Pos.Raw
  deriving Inhabited

/--
Toggle membership of a in the `HashSet` `h`.
If `a ∈ h`, it is removed; otherwise it is inserted.
-/
def toggle {α} [BEq α] [Hashable α] (h : Std.HashSet α) (a : α) :=
  if h.contains a then h.erase a else h.insert a

/--
Insert a `(range, kind)` pair into the `RangesToKinds` structure.
This:
* records that the command with kind `k` occupies `rg` in `toKinds`;
* toggles both `rg.start` and `rg.stop` in `mod2` (so each complete range contributes
  an even parity overall);
* preserves the previously computed `importEnd`.
-/
def RangesToKinds.insert (h : RangesToKinds) (rg : Syntax.Range) (k : Name) : RangesToKinds where
  toKinds := h.toKinds.insert rg k
  mod2 := toggle (toggle h.mod2 rg.start) rg.stop
  importEnd := h.importEnd

/--
Global reference used to accumulate top-level command ranges and kinds while the file is
being elaborated. It starts empty and is progressively populated by the linter.
-/
initialize toKindsRef : IO.Ref RangesToKinds ← IO.mkRef {toKinds := ∅, mod2 := ∅, importEnd := none}

namespace GlobalSyntax

/-- A convenience pretty-printer for `Syntax.Range` used in diagnostic messages. -/
local instance : ToString Syntax.Range where
  toString := fun | {start, stop} => s!"({start}, {stop})"

/--
A convenience pretty-printer for `RangesToKinds` used for debugging (if needed).
It shows all the fields of the input `RangesToKinds`.
-/
local instance : ToString RangesToKinds where
  toString := fun
  | {toKinds := toKs, mod2 := m2, importEnd := pos?} =>
    let sorted := toKs.toArray.qsort (·.1.start < ·.1.start)
    s!"{if let some pos := pos? then s!"{pos}" else ""}\n\
    mod2: {m2.toArray.qsort}\n\n\
    toKinds:\n* {"\n* ".intercalate (sorted.map (s!"{·}")).toList}"

/--
Mapping from starting command kinds to the array of ending command kinds that may close
them at the top level. The linter uses this to recognize trivial
"start immediately followed by end" pairs that have no global effect.
Examples:
* `Parser.Command.namespace` closes with `Parser.Command.end`;
* one-line commands like `open`, `variable`, and `universe` may be followed by either
  `end` (ending a surrounding block) or end-of-input `eoi`.
-/
abbrev startersEnders : NameMap (Array Name) := .ofArray (cmp := Name.quickCmp) #[
    (``Parser.Command.namespace, #[``Parser.Command.end]),
    (``Parser.Command.section, #[``Parser.Command.end]),
    (``Parser.Command.open, #[``Parser.Command.end, ``Parser.Command.eoi]),
    (``Parser.Command.variable, #[``Parser.Command.end, ``Parser.Command.eoi]),
    (``Parser.Command.universe, #[``Parser.Command.end, ``Parser.Command.eoi]),
  ]

/--
Compute all adjacent cancelling pairs from a sorted array of `(range, kind)` pairs.

Given an array `h` of top-level commands sorted by increasing `range.start`, this returns
every pair `(rg₁, rg₂)` such that the command of kind `h[i].2` is immediately followed by an
"ender" kind that cancels it (according to `startersEnders`).

Only adjacent pairs are considered.
-/
def cancellingPairs (h : Array (Syntax.Range × Name)) :
    Array (Syntax.Range × Syntax.Range) := Id.run do
  if this : h.size ≤ 1 then return #[] else
  let mut pairs := #[]
  let mut curr := h[0]
  for i in [:h.size - 1] do
    curr := h[i]!
    let next := h[i + 1]!
    if let some ender := startersEnders.get? curr.2 then
      if ender.contains next.2 then
        pairs := pairs.push (curr.1, next.1)
    curr := next
  return pairs

/--
Return the trimmed substring of `s` delimited by the `Syntax.Range` `rg`.
This is used by the linter to echo the exact command text in diagnostic messages.
-/
def substringOfRange (s : String) (rg : Syntax.Range) : String :=
  {s.toRawSubstring with startPos := rg.start, stopPos := rg.stop}.trim.toString

-- Note that we explicitly avoid `withSetOptionIn`, since we want to inspect the outermost
-- commands.
@[inherit_doc Mathlib.Linter.linter.globalSyntax]
def globalSyntaxLinter : Linter where run stx := do
  unless Linter.getLinterValue linter.globalSyntax (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if (← toKindsRef.get).toKinds.isEmpty then
    let fm ← getFileMap
    let (_, pos, _) ← parseImports fm.source
    let posStx := fm.ofPosition pos
    toKindsRef.modify (fun r => {r with toKinds := r.toKinds.insert ⟨0, posStx⟩ `Module, importEnd := some posStx})
  if let some rg := stx.getRangeWithTrailing? then
    -- `rg.stop == 0` should only happen when parsing `eoi`. In that case, `stx.getRange?` is
    -- the range of width `0` at the end of the file.
    let rg' := if rg.stop == 0 then stx.getRange?.getD default else rg
    toKindsRef.modify (·.insert rg' stx.getKind)
  let kindsRef ← toKindsRef.get
  let fm ← getFileMap
  unless kindsRef.mod2.size == 2 &&
      (kindsRef.mod2.toArray.qsort == #[kindsRef.importEnd.getD 0, fm.positions.back!]) do
    return
  for (rg1, rg2) in cancellingPairs <| kindsRef.toKinds.toArray.qsort (·.1.start < ·.1.start) do
    -- No range should have stopping position strictly before its ending position.
    if rg1.stop < rg1.start || rg2.stop < rg2.start then
      logWarning "This should not have happened"
      continue
    logLint linter.globalSyntax (.ofRange rg1)
      m!"The command '{substringOfRange fm.source rg1}'"
    logLint linter.globalSyntax (.ofRange rg2)
      m!"is cancelled by '{substringOfRange fm.source rg2}'!"

initialize addLinter globalSyntaxLinter

end GlobalSyntax

end Mathlib.Linter
