/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

module

import Mathlib.Init

/-! # Test file for the Verso forward reference linter

If a name in a Verso docstring is assigned a `scope`, this name only gets checked later by the
deferred linter. This file should raise a pair of warnings, and we check that this actually happens
as part of Mathlib CI.
-/

set_option doc.verso true

-- These two should give errors in the docstring below, let's make sure they really do not exist.
assert_not_exists NonexistentName
assert_not_exists NonexistentNameInNonexistentModule

/-- {name}`foo` is a {name}`Nat` but could be a {name (scope := "Mathlib.Data.Real.Basic")}`Real`
or a {name (scope := "Mathlib.Data.Real.Basic")}`NonexistentName` or a
{name (scope := "Module.Does.Not.Exist")}`NonexistentNameInNonexistentModule`. -/
public def foo : Nat := 1
