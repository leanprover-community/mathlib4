/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Environment
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Additional utilities for `Lean.Environment`
-/

namespace Lean.Environment

public section constKind

/- The following declarations account for the fact that the `ConstantKind` of a declaration is
accessible when getting its `ConstantVal`, but is not recorded in said `ConstantVal`. -/

/--
Like `findConstVal?`, but also returns the declarations `ConstantKind`, which is known immediately.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def findConstValWithKind? (env : Environment) (decl : Name) (skipRealize := false) :
    Option (ConstantVal × ConstantKind) := do
  let info ← env.findAsync? decl skipRealize
  return (info.toConstantVal, info.kind)

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if its kind satisfies
`p`. Otherwise, returns `none`.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def findConstValOfKind? (env : Environment) (p : ConstantKind → Bool) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  let info ← env.findAsync? decl skipRealize
  if p info.kind then info.toConstantVal else none

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if it is a theorem.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def findTheoremConstVal? (env : Environment) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  env.findConstValOfKind? (· matches .thm) decl skipRealize

end constKind

end Environment

public section envT

-- I kind of want a "one-way abbrev" here, where `EnvT` has all the instances `StateT Environment` has but not vice-versa...
/-- An abbreviation for `StateT Environment` with a `MonadEnv` instance. -/
abbrev EnvT := StateT Environment

instance {m} [Monad m] : MonadEnv (EnvT m) where
  getEnv := get
  modifyEnv := modify

/-- Runs an `EnvT := StateT Environment` action with the supplied `Environment`.

A monad-generic action `x` of type `[MonadEnv m] → m α` may be run with `EnvT.run (env := env) x`,
or alternatively with dot notation as `env.run x` via the alias `Environment.run`. See also
`env.runPure` for use in pure contexts (`m := Id`). -/
nonrec def EnvT.run.{v} {m : Type → Type v} {α : Type} (x : EnvT m α) (env : Environment) :
    m (α × Environment) := x.run env

/-- Runs an `EnvT := StateT Environment` action with the supplied `Environment`, discarding the
resulting `Environment`.

A monad-generic action `x` of type `[MonadEnv m] → m α` may be run with `EnvT.run' (env := env) x`,
or alternatively with dot notation as `env.run' x` via the alias `Environment.run'`. See also
`env.runPure'` for use in pure contexts (`m := Id`) without the `Id` annotation, for convenience. -/
nonrec def EnvT.run'.{v} {m : Type → Type v} [Functor m] {α : Type} (x : EnvT m α)
    (env : Environment) : m α := x.run' env

namespace Environment

export EnvT (run run')

/-- Runs a monad-generic action `x : [MonadEnv m] → m α` with `env` as the state of the monad. -/
@[inline] def runPure {α : Type} (x : EnvT Id α)
    (env : Environment) : α × Environment := x.run env

/-- Runs a monad-generic action `x : [MonadEnv m] → m α` with `env` as the state of the monad,
discarding the resulting environment. -/
@[inline] def runPure' {α : Type} (x : EnvT Id α)
    (env : Environment) : α := x.run' env

end Environment

end envT

end Lean
