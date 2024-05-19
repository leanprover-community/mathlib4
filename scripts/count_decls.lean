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

/-- A structure to tally declaration types:
* `thms` are theorems;
* `preds` are predicates;
* `types` are types;
* `data` is everything else.
-/
structure Tally where
  thms  : HashSet Name := {}
  data  : HashSet Name := {}
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
  Theorems\n\
  {print t.thms}\n\
  Data\n\
  {print t.data}\n\
  Predicates\n\
  {print t.preds}\n\
  Types\n\
  {print t.types}"

/-- Extend a `Tally` by the ConstantInfo `c`.  It is written to work with `Lean.SMap.foldM`. -/
def updateTally (s : Tally) (n : Name) (c : ConstantInfo) :
    MetaM Tally := do
  if c.isUnsafe || (← n.isBlackListed) then return s else
  let typ := c.type
  if (← isProp typ) then
    return {s with thms := s.thms.insert  n}
  else
    forallTelescopeReducing typ fun _ exp' => do
      if exp'.isType then
        return {s with types := s.types.insert n}
      else
      if exp'.isSort then
        return {s with preds := s.preds.insert n}
      else
        return {s with data := s.data.insert n}

/-- extends a `Tally` all the `ConstantInfos` in the environment. -/
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
