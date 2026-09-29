module

public meta import Lean
public import Mathlib.Init

/-!
# `InfoTree` linting framework
-/

open Lean Elab Command

namespace Mathlib.Linter

public section

structure Infos where

structure InfoLinter where
  name : Name := by exact decl_name%
  run : Infos → Syntax → CommandElabM Unit

initialize infoLintersRef : IO.Ref (Array InfoLinter) ← IO.mkRef #[]

@[inline] def addInfoLinter (l : InfoLinter) : IO Unit :=
  infoLintersRef.modify fun ls => ls.push l

def infoLinterRunner : Linter where
  run stx :=
    let infos : Infos := sorry
    -- withtracenode
    for l in ← infoLintersRef.get do
      try
        l.run infos stx
      catch ex =>
        logError m!"InfoTree linter `{.ofConstName l.name}` failed:{indentD ex.toMessageData}"
