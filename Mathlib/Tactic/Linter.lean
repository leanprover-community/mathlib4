/-
This is the `Linter`s file: it imports files defining linters.
Most syntax linters, in particular the ones enabled by default, are imported in `Mathlib.Init`;
this file contains all linters not imported in that file.

This file is ignored by `shake`:
* it is in `ignoreAll`, meaning that all its imports are considered necessary;
* it is in `ignoreImport`, meaning that where it is imported, it is considered necessary.
-/
module

public import Mathlib.Tactic.Linter.DeprecatedModule
public import Mathlib.Tactic.Linter.HaveLetLinter
public import Mathlib.Tactic.Linter.MinImports
public import Mathlib.Tactic.Linter.PPRoundtrip
public import Mathlib.Tactic.Linter.PrivateModule
public import Mathlib.Tactic.Linter.UnusedInstancesInType
public import Mathlib.Tactic.Linter.UpstreamableDecl
