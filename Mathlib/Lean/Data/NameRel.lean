/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Lean.Data.NameMap
import Lean.Declaration
import Mathlib.Lean.Expr.Basic

/-!
## A data structure for a relation on names
-/

open Lean Meta

namespace Lean

/-- A `NameRel` maps names to sets of names -/
def NameRel := NameMap NameSet

instance : EmptyCollection NameRel :=
  inferInstanceAs $ EmptyCollection (NameMap NameSet)

instance : Inhabited NameRel :=
  inferInstanceAs $ Inhabited (NameMap NameSet)

/-- Finds the set of names associated with the given one -/
def NameRel.find (m : NameRel) (n : Name) : NameSet := m.findD n {}

def NameRel.insert (m : NameRel) (n₁ n₂ : Name) : NameRel :=
  m.find n₁ |>.insert n₂ |> NameMap.insert m n₁

end Lean
