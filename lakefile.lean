import Lake

open Lake DSL

package mathlib

@[defaultTarget]
lean_lib Mathlib

@[defaultTarget]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true
