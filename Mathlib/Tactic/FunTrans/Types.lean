/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types

/-!
## `funTrans`
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunTrans

@[extern "mathlib_fun_trans"]
opaque funTrans (e : Expr) : SimpM Simp.Step
