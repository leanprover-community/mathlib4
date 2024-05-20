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
* `dprop` are `def`s that are in `Prop`;
* `dpred` are `def`s that are predicates;
* `dtype` are `def`s that are types;
* `ddata` are all remaining `def`s;
* `thms`  are non-`def`s that are in `Prop`;
* `preds` are non-`def`s that are predicates;
* `types` are non-`def`s that are types;
* `data` is everything else.
-/
structure Tally where
  dprop : HashSet Name := {}
  dtype : HashSet Name := {}
  dpred : HashSet Name := {}
  ddata : HashSet Name := {}
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
  Definitions-Data\n\
  {print t.ddata}\n\
  Data\n\
  {print t.data}\n\
  Definitions-Props\n\
  {print t.dprop}\n\
  Types\n\
  {print t.types}\n\
  Definitions-Types\n\
  {print t.dtype}\n\
  Predicates\n\
  {print t.preds}\n\
  Definitions-Predicates\n\
  {print t.dpred}"

/-- `declKind` is the inductive enumerating the possibilities for a declaration. -/
inductive declKind
  /-- `dprop` is a `def` that is in `Prop` -/
  | dprop
  /-- `dpred` is a `def` that is predicates -/
  | dpred
  /-- `dtype` is a `def` that is types -/
  | dtype
  /-- `ddata` are all remaining `def`s -/
  | ddata
  /-- `thm` is non-`def` that is in `Prop` -/
  | thm
  /-- `pred` is non-`def` that is a predicate -/
  | pred
  /-- `type` is non-`def` that is a type -/
  | type
  /-- `data` is everything else -/
  | data

/-- `toDeclKind c` classifies the `ConstantInfo` `c` into its `declKind`. -/
def toDeclKind (c : ConstantInfo) : MetaM declKind := do
  let typ := c.type
  if let .defnInfo .. := c then
    if (← isProp typ) then return .dprop else
    if typ.isType then return .dtype else
    if typ.isSort then return .dpred
    else return .ddata
  else
    if (← isProp typ) then return .thm else
    if typ.isType then return .type else
    if typ.isSort then return .pred
    else return .data

/-- Extend a `Tally` by the ConstantInfo `c`.  It is written to work with `Lean.SMap.foldM`. -/
def updateTally (s : Tally) (_ : Name) (c : ConstantInfo) : MetaM Tally := do
  let n := c.name
  if c.isUnsafe || (← n.isBlackListed) then return s else
  match ← toDeclKind c with
    | .thm   => return {s with thms  := s.thms.insert n}
    | .type  => return {s with types := s.types.insert n}
    | .pred  => return {s with preds := s.preds.insert n}
    | .data  => return {s with data  := s.data.insert n}
    | .dprop => return {s with dprop := s.dprop.insert n}
    | .dtype => return {s with dtype := s.dtype.insert n}
    | .dpred => return {s with dpred := s.dpred.insert n}
    | .ddata => return {s with ddata := s.ddata.insert n}

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
