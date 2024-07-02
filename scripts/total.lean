/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib

/-!
Find the declarations that are not used by any other declaration
-/

open Lean
#eval show CoreM _ from do
  dbg_trace (Tips.tips (← getEnv)).toList
