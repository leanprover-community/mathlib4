/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
This file only produces noise that is undetected by CI
-/

open Lean in
run_cmd
  for msg in ["", "hello"] do
    logInfo msg
--    logWarning msg
--    logError msg
