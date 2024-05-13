import Lean.Elab.Command

open Lean in
run_cmd
  for msg in ["", "hello"] do
    logInfo msg
--    logWarning msg
--    logError msg
