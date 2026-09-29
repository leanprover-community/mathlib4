module

public meta import Lean
public import Mathlib.Init

/-!
# `InfoTree` linting framework
-/

open Lean Elab Command

namespace Mathlib.Linter

structure Infos where
