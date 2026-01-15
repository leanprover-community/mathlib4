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
and similarly for consecutive pairs of `open`or `section` and `end`.
-/

public meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The "globalSyntax" linter emits a warning on pairs of consecuting commands with no overall effect.

For instance, the linter would flag
```lean4
namespace X
end X
```
and similarly for consecutive pairs of `open`or `section` and `end`.
-/
public register_option linter.globalSyntax : Bool := {
  defValue := true
  descr := "enable the globalSyntax linter"
}

structure RangesToKinds where
  toKinds : Std.HashMap Syntax.Range Name
  mod2 : Std.HashSet String.Pos.Raw
  importEnd : Option String.Pos.Raw
  deriving Inhabited

def toggle {α} [BEq α] [Hashable α] (h : Std.HashSet α) (a : α) :=
  if h.contains a then h.erase a else h.insert a

def RangesToKinds.insert (h : RangesToKinds) (rg : Syntax.Range) (k : Name) : RangesToKinds where
  toKinds := h.toKinds.insert rg k
  mod2 := toggle (toggle h.mod2 rg.start) rg.stop
  importEnd := h.importEnd

initialize toKindsRef : IO.Ref RangesToKinds ← IO.mkRef {toKinds := ∅, mod2 := ∅, importEnd := none}

namespace GlobalSyntax

local instance : ToString Syntax.Range where
  toString := fun | {start, stop} => s!"({start}, {stop})"

local instance : ToString RangesToKinds where
  toString := fun
  | {toKinds := toKs, mod2 := m2, importEnd := pos?} =>
    let sorted := toKs.toArray.qsort (·.1.start < ·.1.start)
    s!"{if let some pos := pos? then s!"{pos}" else ""}\n\
    mod2: {m2.toArray.qsort}\n\n\
    toKinds:\n* {"\n* ".intercalate (sorted.map (s!"{·}")).toList}"

abbrev startersEnders : NameMap Name := .ofArray (cmp := Name.quickCmp) #[
    (``Parser.Command.namespace, ``Parser.Command.end),
    (``Parser.Command.open, ``Parser.Command.end),
    (``Parser.Command.section, ``Parser.Command.end),
    (``Parser.Command.variable, ``Parser.Command.end),
  ]

def cancellingPairs (h : Array (Syntax.Range × Name)) :
    Array (Syntax.Range × Syntax.Range) := Id.run do
  if this : h.size ≤ 1 then return #[] else
  let mut pairs := #[]
  let mut curr := h[0]
  for i in [:h.size - 1] do
    curr := h[i]!
    let next := h[i + 1]!
    if let some ender := startersEnders.get? curr.2 then
      if next.2 == ender then
      pairs := pairs.push (curr.1, next.1)
    curr := next
  return pairs

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
    toKindsRef.modify (·.insert rg stx.getKind)
  let kindsRef ← toKindsRef.get
  unless kindsRef.mod2.size == 2 && (kindsRef.mod2.toArray.qsort == #[0, kindsRef.importEnd.getD 0]) do
    return
  for (rg1, rg2) in cancellingPairs <| kindsRef.toKinds.toArray.qsort (·.1.start < ·.1.start) do
    logLint linter.globalSyntax (.ofRange rg1) "This command"
    logLint linter.globalSyntax (.ofRange rg2) "is cancelled by this one!"

initialize addLinter globalSyntaxLinter

end GlobalSyntax

end Mathlib.Linter
