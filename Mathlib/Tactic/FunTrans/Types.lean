/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types

import Mathlib.Tactic.FunProp.Types

/-!
## `funTrans`
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunTrans


structure Config where
  funPropConfig : FunProp.Config := {}
deriving Inhabited

initialize funTransConfig : IO.Ref Config ← IO.mkRef {}
