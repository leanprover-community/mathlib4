/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Init
import Qq
import Mathlib.Util.AssertExists

/--
warning: Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Lint.Basic,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Lint.Basic is imported by Batteries.Tactic.Lint.Misc,
which is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Lint.Misc,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Lint.Misc is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.OpenPrivate,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.OpenPrivate is imported by Batteries.Tactic.Lint.Simp,
which is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Util.LibraryNote,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Util.LibraryNote is imported by Batteries.Tactic.Lint.Simp,
which is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Lint.Simp,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Lint.Simp is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Lint.TypeClass,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Lint.TypeClass is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Lint.Frontend,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Lint.Frontend is imported by Batteries.Tactic.Lint,
which is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Lint,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Lint is imported by Mathlib.Tactic.Linter.Lint,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Batteries.Tactic.Unreachable,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Batteries.Tactic.Unreachable is imported by Mathlib.Tactic.Linter.UnusedTactic,
which is imported by Mathlib.Init,
which is imported by Mathlib.Util.AssertExistsExt,
which is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Mathlib.Util.AssertExistsExt,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Mathlib.Util.AssertExistsExt is imported by Mathlib.Util.AssertExists,
which is imported by this module.

Module MathlibTest.DirectoryDependencyLinter.Test depends on Mathlib.Util.AssertExists,
but is only allowed to import modules starting with one of [Mathlib.Lean].
Note: module Mathlib.Util.AssertExists is directly imported by this module
note: this linter can be disabled with `set_option linter.directoryDependency false`
---
warning: The module doc-string for a file should be the first command after the imports.
Please, add a module doc-string before `/-!# Tests for the `directoryDependency` linter
-/
`.
note: this linter can be disabled with `set_option linter.style.header false`
-/
#guard_msgs in
set_option linter.style.header true in

/-!
# Tests for the `directoryDependency` linter
-/

-- Some unit-tests for internal functions.
#guard Lean.Name.isPrefixOf `Mathlib.Util `Mathlib.Util.Basic == true
#guard Lean.Name.isPrefixOf `Mathlib.Util `Mathlib.Util.Nested.Basic == true
#guard Lean.Name.isPrefixOf `Mathlib.Util `Mathlib.Utils.Basic == false
#guard Lean.Name.isPrefixOf `Mathlib.Foo `Mathlib.Util.Foo == false
#guard Lean.Name.isPrefixOf `Mathlib.Util `Mathlib.Utils == false
