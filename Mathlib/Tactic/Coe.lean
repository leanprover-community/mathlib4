/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

open Lean Elab Term

/-!
Redefine the ↑-notation to elaborate in the same way as type annotations
(i.e., unfolding the coercion instance).
-/

namespace Lean.Elab.Term.CoeImpl

scoped elab "coe%" x:term : term <= expectedType => do
  tryPostponeIfMVar expectedType
  let x ← elabTerm x none
  synthesizeSyntheticMVarsUsingDefault
  ensureHasType expectedType x

macro_rules
  | `(↑ $x) => `(coe% $x)
