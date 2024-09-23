/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Lean.Elab.Command
import Lean.Meta.Instances

/-!
# `no_instances` command

Do not add any instances to the environment.
-/

namespace Lean.Elab.Command

open Meta

/-- Do not add any instances to the environment. -/
elab "no_instances " cmd:command : command => do
  let globalInstances := globalInstanceExtension.ext.toEnvExtension.getState (← getEnv)
  let instances := instanceExtension.ext.toEnvExtension.getState (← getEnv)
  Lean.Elab.Command.elabCommand cmd
  setEnv (globalInstanceExtension.ext.toEnvExtension.setState (← getEnv) globalInstances)
  setEnv (instanceExtension.ext.toEnvExtension.setState (← getEnv) instances)

end Lean.Elab.Command
