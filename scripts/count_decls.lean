/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Damiano Testa
-/
import Mathlib

/-!
# `count_decls` -- a tally of declarations in `Mathlib`

This file is used by the `Periodic reports` script to generate a tally of declarations
in `Mathlib`, `Batteries` and core.

Source: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Metamathematics.3A.20Theorems.20by.20Domain.20Areas/near/374090639
-/

namespace PeriodicReports
open Lean Elab Meta

/-- A structure to tally declaration types.
* `props` are declarations that are in `Prop`;
* `preds` are declarations that are predicates;
* `types` are declarations that are types;
* `defns` are all remaining declarations.
-/
structure Tally where
  props : HashSet Name := {}
  defns : HashSet Name := {}
  preds : HashSet Name := {}
  types : HashSet Name := {}

/-- `toString t` produces a string where each line is either
* the (human-readable) name of a field of `t : Tally`, or
* the name of a single declaration followed by `,`.

The script to extract comparison data relies on the format
* lines ending with `,` or not,
* single declaration per line.
-/
def toString (t : Tally) : String :=
  let print (h : HashSet Name) : String :=
    let tot := h.toList.map (·.toString)
    String.intercalate ",\n" tot ++ ","
  s!"\
  Propositions\n\
  {print t.props}\n\
  Definitions\n\
  {print t.defns}\n\
  Predicates\n\
  {print t.preds}\n\
  Types\n\
  {print t.types}"

/-- Extend a `Tally` by the ConstantInfo `c`.  It is written to work with `Lean.SMap.foldM`. -/
def updateTally (s : Tally) (_ : Name) (c : ConstantInfo) : MetaM Tally := do
  let n := c.name
  if c.isUnsafe || (← n.isBlackListed) then return s else
  let typ := c.type
  if ← isProp typ then return {s with props := s.props.insert n}
  forallTelescopeReducing typ fun _ exp => do
    if exp.isType then return {s with types := s.types.insert n}
    if exp.isSort then return {s with preds := s.preds.insert n}
    else               return {s with defns := s.defns.insert n}

/-- `mkTally s` extends the `Tally` `s` using all the `ConstantInfos` in the environment. -/
def mkTally (s : Tally) : MetaM Tally := do
  let env ← getEnv
  let consts := env.constants
  consts.foldM updateTally s

/-- `count_decls` prints a tally of theorems, types, predicates and data in
`Mathlib`, `Batteries` and core. -/
elab "count_decls" : command => do
  let (s, _) ← Command.liftCoreM do MetaM.run do (mkTally {})
  IO.println (toString s)

--count_decls

end PeriodicReports
