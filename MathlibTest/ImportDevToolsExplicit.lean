module

public import Mathlib
public import ImportGraph.Lean.Environment

-- An explicit ordinary import makes the representative definition rejected in
-- `ImportDevTools.lean` valid. This rules out rejection solely because the API is intrinsically meta.
public def importGraphExplicit (env : Lean.Environment) (name : Lean.Name) : Option Lean.Name :=
  env.getModuleFor? name
