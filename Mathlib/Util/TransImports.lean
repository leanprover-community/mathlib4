import Lean.Elab.Command

open Lean in
/--
`#trans_imports` reports how many transitive imports the current module has.
The command takes an optional string input: `#trans_imports str` also shows the transitively
imported modules whose name begins with `str`.
-/
elab tk:"#trans_imports" stx:(str)? : command => do
  let imports := (← getEnv).allImportedModuleNames
  let currMod := if let mod@(.str _ _) := ← getMainModule then m!"'{mod}' has " else ""
  let rest := match stx with
      | none => m!""
      | some str =>
        let imps := imports.filterMap fun (i : Name) =>
          if i.toString.startsWith str.getString then some i else none
        m!"\n\n{imps.size} starting with {str}:\n{imps.qsort (·.toString < ·.toString)}"
  logInfoAt tk m!"{currMod}{imports.size} transitive imports{rest}"
