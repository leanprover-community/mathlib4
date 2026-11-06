module

import Mathlib.Tactic.Linter.PrivateModule

open Lean

set_option linter.privateModule true

-- Should not fire, since `initialize` has effects downstream despite creating a private decl here.
initialize pure ()

/- Check that we have indeed created a declaration, and aren't not linting just due to being an
empty file: -/
/-- info: [initFn✝] -/
#guard_msgs in
run_cmd do
  logInfo m!"{(← getEnv).constants.map₂.toArray.map (MessageData.ofConstName ·.1)}"
