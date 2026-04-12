module

import Mathlib.Tactic.Linter.PrivateModule

set_option linter.privateModule false -- Changed in nightly-testing, as this test no longer works.

open Lean

-- Should not fire, since `initialize` creates a genuinely public declaration.
initialize pure ()

/- Check that we have indeed created a declaration, and aren't not linting just due to being an
empty file: -/
/-- info: [initFn✝] -/
#guard_msgs in
run_cmd do
  logInfo m!"{(← getEnv).constants.map₂.toArray.map (MessageData.ofConstName ·.1)}"
