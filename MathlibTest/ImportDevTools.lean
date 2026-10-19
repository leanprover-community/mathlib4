module

public import Mathlib

/-
These tests check representative declarations, not every declaration in the dependencies.
Other declarations could become available at runtime without these tests noticing.
-/

/--
error: Invalid definition `importGraphRuntime`, may not access declaration `Lean.Environment.getModuleFor?` imported as `meta`; consider adding `import ImportGraph.Lean.Environment`
-/
#guard_msgs in
public def importGraphRuntime (env : Lean.Environment) (name : Lean.Name) : Option Lean.Name :=
  env.getModuleFor? name

-- The same API remains usable during elaboration.
public meta def importGraphMeta (env : Lean.Environment) (name : Lean.Name) : Option Lean.Name :=
  env.getModuleFor? name

-- LeanSearchClient declares this API `meta` upstream, so this checks its phase rather than
-- detecting ordinary imports. An ordinary import cannot enable runtime use of this declaration.
/--
error: Invalid definition `leanSearchRuntime`, may not access declaration `LeanSearchClient.useragent` marked as `meta`
-/
#guard_msgs in
public def leanSearchRuntime : Lean.CoreM String := LeanSearchClient.useragent

public meta def leanSearchMeta : Lean.CoreM String := LeanSearchClient.useragent
