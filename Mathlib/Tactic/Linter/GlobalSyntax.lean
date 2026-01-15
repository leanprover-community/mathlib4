module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Elab.Import
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
  deriving Inhabited

def toggle {α} [BEq α] [Hashable α] (h : Std.HashSet α) (a : α) :=
  if h.contains a then h.erase a else h.insert a

def RangesToKinds.insert (h : RangesToKinds) (rg : Syntax.Range) (k : Name) : RangesToKinds where
  toKinds := h.toKinds.insert rg k
  mod2 := toggle (toggle h.mod2 rg.start) rg.stop

initialize toKindsRef : IO.Ref RangesToKinds ← IO.mkRef {toKinds := ∅, mod2 := ∅}

namespace GlobalSyntax

local instance : ToString Syntax.Range where
  toString := fun | {start, stop} => s!"({start}, {stop})"

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
    dbg_trace "current {pos}"
    toKindsRef.modify (·.insert ⟨0, posStx⟩ `Module)
  if let some rg := stx.getRange? then
    toKindsRef.modify (·.insert rg stx.getKind)
  dbg_trace "mod2: {(← toKindsRef.get).mod2.toArray.qsort}"
  dbg_trace "toKinds: {(← toKindsRef.get).toKinds.toArray.qsort (·.1.start < ·.1.start)}"
  --Linter.logLint linter.globalSyntax stx m!"Superfluous pair"

initialize addLinter globalSyntaxLinter

end GlobalSyntax

end Mathlib.Linter
